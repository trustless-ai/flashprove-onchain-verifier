// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC165} from "../interfaces/IERC165.sol";
import {IModelCommitmentAnchor} from "../interfaces/IModelCommitmentAnchor.sol";

/// @title ModelCommitmentAnchor — reference IModelCommitmentAnchor
/// @notice No owner, no upgrade, no fee: one registry any anchorer can write its own rows to.
///         The digest rule is pinned here as `anchorDigest()` so a client and the contract cannot
///         disagree about it; `scripts/recompute-anchor.py` computes the same value from files.
contract ModelCommitmentAnchor is IModelCommitmentAnchor, IERC165 {
    bytes public constant ANCHOR_DOMAIN = "FlashProve/anchor-v1\x00";
    bytes public constant ANCHOR_REF_DOMAIN = "FlashProve/anchor-ref-v1\x00";

    mapping(address => mapping(bytes32 => Anchor)) private _anchors;

    /// @inheritdoc IModelCommitmentAnchor
    function anchor(bytes32 commitmentId, bytes32 digest, string calldata uri) external {
        require(commitmentId != bytes32(0), "FP-ANC: zero commitment ID");
        require(digest != bytes32(0), "FP-ANC: zero digest");
        Anchor storage a = _anchors[msg.sender][commitmentId];
        require(a.anchoredAt == 0, "FP-ANC: already anchored");
        a.anchorDigest = digest;
        a.anchoredAt = uint64(block.timestamp);
        emit Anchored(msg.sender, commitmentId, digest, uri);
    }

    /// @inheritdoc IModelCommitmentAnchor
    function revoke(bytes32 commitmentId, string calldata reason) external {
        Anchor storage a = _anchors[msg.sender][commitmentId];
        require(a.anchoredAt != 0, "FP-ANC: not anchored");
        require(a.revokedAt == 0, "FP-ANC: already revoked");
        a.revokedAt = uint64(block.timestamp);
        emit Revoked(msg.sender, commitmentId, reason);
    }

    /// @inheritdoc IModelCommitmentAnchor
    function anchorOf(address anchorer, bytes32 commitmentId)
        external
        view
        returns (Anchor memory)
    {
        return _anchors[anchorer][commitmentId];
    }

    /// @inheritdoc IModelCommitmentAnchor
    function isLive(address anchorer, bytes32 commitmentId, bytes32 digest)
        external
        view
        returns (bool)
    {
        Anchor storage a = _anchors[anchorer][commitmentId];
        return a.anchoredAt != 0 && a.revokedAt == 0 && a.anchorDigest == digest;
    }

    /// @inheritdoc IModelCommitmentAnchor
    function isAnchored(address anchorer, bytes32 commitmentId) external view returns (bool) {
        Anchor storage a = _anchors[anchorer][commitmentId];
        return a.anchoredAt != 0 && a.revokedAt == 0;
    }

    /// @notice The digest rule, from the per-file SHA-256 values.
    function anchorDigest(
        bytes32 policySha,
        bytes32 layoutSha,
        bytes32 klSha,
        bytes32 keySha,
        bytes32[] calldata leafShas
    ) external pure returns (bytes32) {
        require(leafShas.length <= type(uint32).max, "FP-ANC: too many leaves");
        uint32 n = uint32(leafShas.length);
        bytes memory nle = abi.encodePacked(uint8(n), uint8(n >> 8), uint8(n >> 16), uint8(n >> 24));
        return
            sha256(
                abi.encodePacked(ANCHOR_DOMAIN, policySha, layoutSha, klSha, keySha, nle, leafShas)
            );
    }

    /// @inheritdoc IModelCommitmentAnchor
    function anchorRef(address anchorer, bytes32 commitmentId) external view returns (bytes32) {
        return anchorRefFor(block.chainid, address(this), anchorer, commitmentId);
    }

    /// @notice The anchorRef rule for any deployment, pinned here so a client and the contract cannot
    ///         disagree about it; `scripts/recompute-anchor.py --ref` computes the same value.
    function anchorRefFor(uint256 chainId, address registry, address anchorer, bytes32 commitmentId)
        public
        pure
        returns (bytes32)
    {
        return sha256(abi.encodePacked(ANCHOR_REF_DOMAIN, chainId, registry, anchorer, commitmentId));
    }

    function supportsInterface(bytes4 interfaceId) external pure returns (bool) {
        return interfaceId == type(IModelCommitmentAnchor).interfaceId
            || interfaceId == type(IERC165).interfaceId;
    }
}
