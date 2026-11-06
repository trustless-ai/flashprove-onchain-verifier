// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC165} from "../interfaces/IERC165.sol";
import {IProofVerifier} from "../interfaces/IProofVerifier.sol";

/// @title FlashProveAttestVerifier — ERC-8274 IProofVerifier backed by a signer committee
/// @notice The second verification path in this repository. Instead of a zk proof, a set of
///         pre-approved signers attests that a given input produced a given output, and the
///         contract accepts the inference once enough distinct signers signed the same
///         attestation. It answers the same question the zk path answers — "is this evidence
///         valid for this input and this output" — so both paths plug into the same
///         IAgentVerifier unchanged.
///
/// @dev The attestation preimage is EIP-712 typed data bound to this chain and this deployment, and
///      the proof is `abi.encode(bytes[] signatures)` of 65-byte (r, s, v) ECDSA signatures; both
///      are documented in contracts/README.md ("The attestation path"). The failure mode is the
///      same as the zk path's: return false, never revert, so the outer layer can record the attempt.
///
///      This contract is stateless in the ERC-8274 sense: the committee and the threshold are
///      fixed at deployment and nothing is written afterwards. Rotating the committee means
///      deploying a new instance, which is what gives each deployment its own proofProfile().
///
///      Explicit deviation from IProofVerifier's documentation, declared in the root README:
///      that interface says all deployment configuration arrives through `metadata`, while here
///      the committee and the threshold are constructor arguments and `metadata` carries a
///      32-byte configuration hash. A later maintainer should not read that as a violation.
contract FlashProveAttestVerifier is IProofVerifier, IERC165 {
    /// @notice Proof system identifier, in the "{paradigm}/{variant}" form ERC-8274 asks for.
    string public constant PROOF_SYSTEM = "attestation/multisig";

    /// @notice Number of distinct valid signatures a bundle must carry to be accepted.
    uint256 public immutable threshold;

    /// @notice EIP-712 domain and struct type hashes of the attestation a committee member signs.
    bytes32 public constant DOMAIN_TYPEHASH = keccak256(
        "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
    );
    bytes32 public constant ATTESTATION_TYPEHASH =
        keccak256("Attestation(bytes32 inputHash,bytes32 outputHash,bytes32 metadataHash)");
    bytes32 private constant NAME_HASH = keccak256("FlashProveAttestVerifier");
    bytes32 private constant VERSION_HASH = keccak256("1");

    /// @notice Largest committee a deployment accepts: distinct signers are counted in one
    ///         256-bit word, one bit per committee position.
    uint256 public constant MAX_SIGNERS = 256;

    /// @dev secp256k1 n / 2: signatures with a larger s are the malleable twin and are ignored.
    uint256 private constant HALF_N =
        0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0;

    address[] private _signers;
    /// @dev committee position + 1 (0 = not a signer); written only in the constructor.
    mapping(address => uint256) private _position;

    /// @notice Deployment configuration is unusable: empty committee, zero threshold,
    ///         threshold above the committee size, a committee larger than MAX_SIGNERS, or a
    ///         duplicate/zero signer address.
    error InvalidConfiguration();

    constructor(address[] memory signers_, uint256 threshold_) {
        if (
            signers_.length == 0 || signers_.length > MAX_SIGNERS || threshold_ == 0
                || threshold_ > signers_.length
        ) {
            revert InvalidConfiguration();
        }
        for (uint256 i = 0; i < signers_.length; i++) {
            address signer = signers_[i];
            if (signer == address(0) || _position[signer] != 0) {
                revert InvalidConfiguration();
            }
            _signers.push(signer);
            _position[signer] = _signers.length;
        }
        threshold = threshold_;
    }

    /// @notice The committee, in deployment order.
    function signers() external view returns (address[] memory) {
        return _signers;
    }

    /// @notice Whether an address is allowed to attest on this deployment.
    function isSigner(address account) external view returns (bool) {
        return _position[account] != 0;
    }

    /// @notice The EIP-712 domain separator of this deployment on the current chain. Computed per
    ///         call, so a chain fork changes it and a signature for one chain id never counts on
    ///         another.
    function domainSeparator() public view returns (bytes32) {
        return keccak256(
            abi.encode(DOMAIN_TYPEHASH, NAME_HASH, VERSION_HASH, block.chainid, address(this))
        );
    }

    /// @notice The digest a committee member signs: EIP-712 typed data
    ///         `Attestation(bytes32 inputHash, bytes32 outputHash, bytes32 metadataHash)` under
    ///         the domain {name "FlashProveAttestVerifier", version "1", chainId, this contract}.
    ///         `verify` passes `metadataHash = keccak256(metadata)`.
    function attestationDigest(bytes32 inputHash, bytes32 outputHash, bytes32 metadataHash)
        public
        view
        returns (bytes32)
    {
        bytes32 structHash =
            keccak256(abi.encode(ATTESTATION_TYPEHASH, inputHash, outputHash, metadataHash));
        return keccak256(abi.encodePacked("\x19\x01", domainSeparator(), structHash));
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

    /// @notice Decodes a signature bundle: `abi.encode(bytes[] signatures)`. External so `verify`
    ///         can call it under try/catch and turn a malformed bundle into `false`.
    function decodeBundle(bytes calldata proof) external pure returns (bytes[] memory signatures) {
        return abi.decode(proof, (bytes[]));
    }

    /// @dev Number of DISTINCT committee members with a valid signature over `digest`, counting
    ///      stops at `threshold`. A signature is ignored (never a revert) when it is not exactly
    ///      65 bytes, has v outside {27, 28}, has s above n/2, recovers to address(0) or to a
    ///      non-member, or repeats a member already counted.
    function _countValidSignatures(bytes32 digest, bytes calldata proof)
        private
        view
        returns (uint256 count)
    {
        bytes[] memory sigs;
        try this.decodeBundle(proof) returns (bytes[] memory decoded) {
            sigs = decoded;
        } catch {
            return 0;
        }
        uint256 seen;
        for (uint256 i = 0; i < sigs.length && count < threshold; i++) {
            address signer = _recover(digest, sigs[i]);
            uint256 position = _position[signer];
            if (signer == address(0) || position == 0) {
                continue;
            }
            uint256 bit = uint256(1) << (position - 1);
            if (seen & bit != 0) {
                continue;
            }
            seen |= bit;
            count++;
        }
    }

    /// @dev ecrecover over a 65-byte (r, s, v) signature; address(0) for anything malformed.
    function _recover(bytes32 digest, bytes memory sig) private pure returns (address) {
        if (sig.length != 65) {
            return address(0);
        }
        bytes32 r;
        bytes32 s;
        uint8 v;
        assembly {
            r := mload(add(sig, 0x20))
            s := mload(add(sig, 0x40))
            v := byte(0, mload(add(sig, 0x60)))
        }
        if ((v != 27 && v != 28) || uint256(s) > HALF_N) {
            return address(0);
        }
        return ecrecover(digest, v, r, s);
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
