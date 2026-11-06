// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IAgentProofProfile, IAgentVerifier} from "../interfaces/IAgentVerifier.sol";
import {IERC165} from "../interfaces/IERC165.sol";
import {IProofVerifier} from "../interfaces/IProofVerifier.sol";
import {FlashProvePublicValues} from "../libraries/FlashProvePublicValues.sol";

/// @title ExampleAgentVerifier — ERC-8274 IAgentVerifier for FlashProve
/// @notice The outer, stateful layer. It binds one IProofVerifier, one program vkey (`metadata`),
///         one commitment ID and one accepted-verdict mask, and authorizes a set of agents.
///         A successful verification consumes the task ID; a failed one may be retried.
///
///         `proof` is the SP1 bundle `abi.encode(bytes publicValues, bytes sp1Proof)`. The inner
///         verifier proves that the SP1 circuit produced those public values for the configured
///         program; this contract additionally requires:
///           * the block's commitment ID equals the configured one,
///           * its verdict is in the accepted mask,
///           * its call status is zero (when `requireStatusZero`),
///           * its input and result-v1 digests equal the caller's `inputHash` and `outputHash`.
///
///         `verificationDigest` and the `VerificationCompleted` event follow ERC-8274 exactly.
contract ExampleAgentVerifier is IAgentVerifier, IAgentProofProfile, IERC165 {
    /// @notice The inner proof-system verifier.
    IProofVerifier public immutable verifier;
    /// @notice The invariant metadata passed to the inner verifier: abi.encode(programVKey).
    bytes public metadata;
    /// @notice The FlashProve commitment ID this deployment verifies.
    bytes32 public immutable commitmentId;
    /// @notice Bit `code` set for each accepted FPV1 verdict code.
    uint16 public immutable acceptedVerdicts;
    /// @notice Whether an accepted call must also have call status zero.
    bool public immutable requireStatusZero;

    mapping(bytes32 => bool) public authorizedAgents;
    mapping(bytes32 => bool) public usedTasks;

    bytes32 private immutable _profile;

    constructor(
        IProofVerifier verifier_,
        bytes memory metadata_,
        bytes32 commitmentId_,
        uint16 acceptedVerdicts_,
        bool requireStatusZero_,
        bytes32[] memory authorizedAgents_
    ) {
        require(address(verifier_) != address(0), "FP-AV: zero verifier");
        require(metadata_.length == 32, "FP-AV: metadata must be one program vkey");
        require(acceptedVerdicts_ != 0, "FP-AV: no accepted verdict");

        verifier = verifier_;
        metadata = metadata_;
        commitmentId = commitmentId_;
        acceptedVerdicts = acceptedVerdicts_;
        requireStatusZero = requireStatusZero_;
        for (uint256 i = 0; i < authorizedAgents_.length; i++) {
            authorizedAgents[authorizedAgents_[i]] = true;
        }
        _profile = keccak256(
            abi.encode(address(verifier_), verifier_.proofProfile(), keccak256(metadata_))
        );
    }

    /// @inheritdoc IAgentProofProfile
    function agentProofProfile() external view returns (bytes32) {
        return _profile;
    }

    /// @inheritdoc IAgentVerifier
    function verify(
        bytes32 taskId,
        bytes32 agentId,
        bytes32 inputHash,
        bytes32 outputHash,
        bytes calldata proof
    ) external returns (bool valid, bytes32 verificationDigest) {
        if (!usedTasks[taskId] && authorizedAgents[agentId]) {
            bool innerOk;
            try verifier.verify(inputHash, outputHash, metadata, proof) returns (bool ok) {
                innerOk = ok;
            } catch {
                innerOk = false;
            }
            if (innerOk) {
                try this.checkBinding(proof, inputHash, outputHash) returns (bool ok) {
                    valid = ok;
                } catch {
                    valid = false;
                }
            }
            if (valid) {
                usedTasks[taskId] = true;
            }
        }

        bytes memory instanceId = abi.encodePacked(address(this));
        bytes memory chainId = abi.encode(block.chainid);
        verificationDigest = keccak256(
            abi.encode(
                taskId,
                agentId,
                inputHash,
                outputHash,
                valid,
                _profile,
                block.timestamp,
                instanceId,
                chainId
            )
        );
        emit VerificationCompleted(
            taskId,
            agentId,
            verificationDigest,
            valid,
            inputHash,
            outputHash,
            _profile,
            block.timestamp,
            instanceId,
            chainId
        );
    }

    /// @notice The application checks on the decoded FPV1 block. External so `verify` can turn a
    ///         malformed block into `valid = false` instead of a revert.
    function checkBinding(
        bytes calldata proof,
        bytes32 inputHash,
        bytes32 outputHash
    ) external view returns (bool) {
        (bytes memory publicValues, ) = abi.decode(proof, (bytes, bytes));
        FlashProvePublicValues.Values memory values = FlashProvePublicValues.decode(publicValues);
        if (values.commitmentId != commitmentId) return false;
        if ((acceptedVerdicts & (uint16(1) << values.verdict)) == 0) return false;
        if (requireStatusZero && values.callStatus != 0) return false;
        return values.inputDigest == inputHash && values.resultV1Digest == outputHash;
    }

    function supportsInterface(bytes4 interfaceId) external pure returns (bool) {
        return
            interfaceId == type(IAgentVerifier).interfaceId ||
            interfaceId == type(IAgentProofProfile).interfaceId ||
            interfaceId == type(IERC165).interfaceId;
    }
}
