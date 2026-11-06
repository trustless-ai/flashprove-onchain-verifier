// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC165} from "../interfaces/IERC165.sol";
import {IProofVerifier} from "../interfaces/IProofVerifier.sol";

/// @title AttestationVerifier — ERC-8274 IProofVerifier backed by a signer committee
/// @notice The second verification path in this repository. Instead of a zk proof, a set of
///         pre-approved signers attests that a given input produced a given output, and the
///         contract accepts the inference once enough distinct signers signed the same
///         attestation. It answers the same question the zk path answers — "is this evidence
///         valid for this input and this output" — so both paths plug into the same
///         IAgentVerifier unchanged.
///
/// @dev Skeleton. The attestation preimage and the signature bundle encoding are owned by the
///      committee design owner; those are the only two TODO markers below. Everything else is
///      final: interface conformance, deployment-time configuration, input guards, and the
///      failure mode (return false, never revert, so the outer layer can record the attempt).
///
///      This contract is stateless in the ERC-8274 sense: the committee and the threshold are
///      fixed at deployment and nothing is written afterwards. Rotating the committee means
///      deploying a new instance, which is what gives each deployment its own proofProfile().
///
///      Explicit deviation from IProofVerifier's documentation, declared in the root README:
///      that interface says all deployment configuration arrives through `metadata`, while here
///      the committee and the threshold are constructor arguments and `metadata` carries a
///      32-byte configuration hash. A later maintainer should not read that as a violation.
contract AttestationVerifier is IProofVerifier, IERC165 {
    /// @notice Proof system identifier, in the "{paradigm}/{variant}" form ERC-8274 asks for.
    string public constant PROOF_SYSTEM = "attestation/multisig";

    /// @notice Number of distinct valid signatures a bundle must carry to be accepted.
    uint256 public immutable threshold;

    address[] private _signers;
    mapping(address => bool) private _isSigner;

    /// @notice Deployment configuration is unusable: empty committee, zero threshold,
    ///         threshold above the committee size, or a duplicate/zero signer address.
    error InvalidConfiguration();

    constructor(address[] memory signers_, uint256 threshold_) {
        if (signers_.length == 0 || threshold_ == 0 || threshold_ > signers_.length) {
            revert InvalidConfiguration();
        }
        for (uint256 i = 0; i < signers_.length; i++) {
            address signer = signers_[i];
            if (signer == address(0) || _isSigner[signer]) {
                revert InvalidConfiguration();
            }
            _isSigner[signer] = true;
            _signers.push(signer);
        }
        threshold = threshold_;
    }

    /// @notice The committee, in deployment order.
    function signers() external view returns (address[] memory) {
        return _signers;
    }

    /// @notice Whether an address is allowed to attest on this deployment.
    function isSigner(address account) external view returns (bool) {
        return _isSigner[account];
    }

    /// @notice The digest a committee member signs.
    /// @dev TODO(committee owner): settle the preimage. Whether the domain should be EIP-712,
    ///      whether metadata enters as a hash or at all, and whether the chain id belongs in
    ///      it are design decisions. Whatever is chosen must be written down in
    ///      contracts/README.md — ERC-8274 requires the commitment scheme to be documented.
    function attestationDigest(
        bytes32 inputHash,
        bytes32 outputHash,
        bytes32 metadataHash
    ) public view returns (bytes32) {
        return keccak256(abi.encode(PROOF_SYSTEM, address(this), inputHash, outputHash, metadataHash));
    }

    /// @inheritdoc IProofVerifier
    /// @dev Unparseable input returns false rather than reverting, so a failed attempt still
    ///      surfaces through the caller's event instead of being swallowed as a revert.
    function verify(
        bytes32 inputHash,
        bytes32 outputHash,
        bytes calldata metadata,
        bytes calldata proof
    ) external view returns (bool) {
        if (metadata.length != 32 || proof.length < 0x80) {
            return false;
        }
        bytes32 digest = attestationDigest(inputHash, outputHash, keccak256(metadata));
        return _countValidSignatures(digest, proof) >= threshold;
    }

    /// @dev TODO(committee owner): decode the bundle, recover each signature, discard
    ///      duplicates and non-signers, and return how many distinct committee members signed
    ///      `digest`. The placeholder returns zero, so no bundle is accepted until this lands.
    function _countValidSignatures(
        bytes32 /* digest */,
        bytes calldata /* proof */
    ) private pure returns (uint256) {
        return 0;
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
