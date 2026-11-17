// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title IModelCommitmentAnchor — on-chain anchor for a FlashProve commitment ID
/// @notice Removes the trusted serving/logging host. An anchorer publishes, once per commitment
///         ID, the digest of the static artifacts that ID was made from (policy, layout, KL, key,
///         and the leaf table). A host then only serves bytes; a client checks the bytes it got
///         against the anchor, and an outer IAgentVerifier refuses a proof whose commitment ID is
///         not live under an anchorer it accepts.
///
///         The anchor never enters the SNARK: the proof keeps proving the computation, the anchor
///         is a separate, cheap comparison. Several anchorers may anchor the same ID
///         independently; the verifier chooses whose anchors count.
///
///         anchorDigest = SHA-256(ANCHOR_DOMAIN
///                                ‖ sha256(policy) ‖ sha256(layout) ‖ sha256(kl) ‖ sha256(key)
///                                ‖ u32le(leafCount) ‖ sha256(leaf_0) ‖ … ‖ sha256(leaf_{n-1}))
///         ANCHOR_DOMAIN = "FlashProve/anchor-v1\0"
///         Fixed-size fields, so no length prefixes are needed; leaves in entry-number order.
interface IModelCommitmentAnchor {
    struct Anchor {
        bytes32 anchorDigest;
        uint64 anchoredAt;
        uint64 revokedAt; // 0 while live
    }

    event Anchored(
        address indexed anchorer, bytes32 indexed commitmentId, bytes32 anchorDigest, string uri
    );
    event Revoked(address indexed anchorer, bytes32 indexed commitmentId, string reason);

    /// @notice Anchor `commitmentId` to `anchorDigest`. Write-once per (anchorer, commitmentId):
    ///         a changed artifact set is a different model commitment, so it gets a new ID.
    /// @param uri Where the artifacts can be fetched (informational; never trusted).
    function anchor(bytes32 commitmentId, bytes32 anchorDigest, string calldata uri) external;

    /// @notice Revoke the caller's own anchor (a recalled model, a leaked or wrong artifact).
    ///         Permanent: a revoked anchor cannot be re-anchored under the same ID.
    function revoke(bytes32 commitmentId, string calldata reason) external;

    function anchorOf(address anchorer, bytes32 commitmentId) external view returns (Anchor memory);

    /// @notice True when `anchorer` anchored `commitmentId` to exactly `anchorDigest` and has not
    ///         revoked it.
    function isLive(address anchorer, bytes32 commitmentId, bytes32 anchorDigest)
        external
        view
        returns (bool);

    /// @notice True when `anchorer` holds a live anchor for `commitmentId` (any digest) — the check
    ///         an outer verifier makes on-chain, where the artifact bytes are not available.
    function isAnchored(address anchorer, bytes32 commitmentId) external view returns (bool);

    /// @notice A stable key naming one anchor ROW, for records that compose with it (e.g. a verifier
    ///         profile anchor keyed on (verifier, proofProfile(), metadata, chainId)). The digest stays
    ///         content-only -- the same artifacts hash the same on every chain -- and the chain lives
    ///         here, in the reference:
    ///         anchorRef = SHA-256(ANCHOR_REF_DOMAIN ‖ u256be(chainId) ‖ registry ‖ anchorer ‖ commitmentId)
    ///         ANCHOR_REF_DOMAIN = "FlashProve/anchor-ref-v1\0"; registry and anchorer are 20 bytes.
    function anchorRef(address anchorer, bytes32 commitmentId) external view returns (bytes32);
}
