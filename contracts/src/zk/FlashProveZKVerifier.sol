// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC165} from "../interfaces/IERC165.sol";
import {IProofVerifier} from "../interfaces/IProofVerifier.sol";
import {ISP1Verifier} from "../interfaces/ISP1Verifier.sol";
import {FlashProvePublicValues} from "../libraries/FlashProvePublicValues.sol";

/// @title FlashProveZKVerifier — ERC-8274 IProofVerifier for FlashProve's SP1 circuit
/// @notice The inner, stateless layer. `metadata` is `abi.encode(bytes32 programVKey)`; `proof`
///         is `abi.encode(bytes publicValues, bytes sp1Proof)` — the bundle `fp-prover` writes.
///         The SP1 verifier checks the proof against the first 128 bytes-plus-prefix public
///         values; this contract then requires the decoded FPV1 block to commit to the caller's
///         `inputHash` and `outputHash`.
/// @dev The application checks — commitment ID, accepted verdicts, call status — belong to the
///      outer IAgentVerifier, not here.
contract FlashProveZKVerifier is IProofVerifier, IERC165 {
    /// @notice The deployed SP1 verifier (the Succinct gateway or a circuit-specific verifier).
    address public immutable sp1Verifier;

    string public constant PROOF_SYSTEM = "zk/sp1";

    constructor(address sp1Verifier_) {
        require(sp1Verifier_ != address(0), "SP1PV: zero verifier");
        sp1Verifier = sp1Verifier_;
    }

    /// @inheritdoc IProofVerifier
    function verify(
        bytes32 inputHash,
        bytes32 outputHash,
        bytes calldata metadata,
        bytes calldata proof
    ) external view returns (bool) {
        if (metadata.length != 32 || proof.length < 0x80) {
            return false;
        }
        bytes32 programVKey = abi.decode(metadata, (bytes32));

        // A malformed bundle must return false, not revert, so the outer layer can emit its
        // event for a failed attempt.
        try this.split(proof) returns (bytes memory publicValues, bytes memory proofBytes) {
            if (publicValues.length < FlashProvePublicValues.LENGTH) {
                return false;
            }
            try ISP1Verifier(sp1Verifier).verifyProof(programVKey, publicValues, proofBytes) {
                // The proof is cryptographically valid for these public values.
            } catch {
                return false;
            }
            try this.decodePublicValues(publicValues) returns (
                FlashProvePublicValues.Values memory values
            ) {
                return
                    values.inputDigest == inputHash && values.resultV1Digest == outputHash;
            } catch {
                return false;
            }
        } catch {
            return false;
        }
    }

    /// @notice Splits the wrapper bundle; external so `verify` can catch a malformed encoding.
    function split(
        bytes calldata bundle
    ) external pure returns (bytes memory publicValues, bytes memory proofBytes) {
        return abi.decode(bundle, (bytes, bytes));
    }

    /// @notice Decodes the FPV1 block; external so `verify` can catch a malformed block.
    function decodePublicValues(
        bytes calldata publicValues
    ) external pure returns (FlashProvePublicValues.Values memory) {
        return FlashProvePublicValues.decode(publicValues);
    }

    /// @inheritdoc IProofVerifier
    function proofSystem() public pure returns (string memory) {
        return PROOF_SYSTEM;
    }

    /// @inheritdoc IProofVerifier
    function proofProfile() external view returns (bytes32) {
        return keccak256(abi.encode(PROOF_SYSTEM, address(this).codehash));
    }

    function supportsInterface(bytes4 interfaceId) external pure returns (bool) {
        return
            interfaceId == type(IProofVerifier).interfaceId ||
            interfaceId == type(IERC165).interfaceId;
    }
}
