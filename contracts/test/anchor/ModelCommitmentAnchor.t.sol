// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {TestBase} from "../utils/TestBase.sol";
import {IERC165} from "../../src/interfaces/IERC165.sol";
import {IModelCommitmentAnchor} from "../../src/interfaces/IModelCommitmentAnchor.sol";
import {ModelCommitmentAnchor} from "../../src/anchor/ModelCommitmentAnchor.sol";

/// @notice The anchor registry: the digest rule against a cross-language vector (the repo's own
///         fixtures, computed by scripts/recompute-anchor.py from the files), write-once, revoke,
///         independence of anchorers, and the two read paths an outer verifier and a client use.
contract ModelCommitmentAnchorTest is TestBase {
    ModelCommitmentAnchor private reg;

    // rust-verifier/fixtures: per-file SHA-256 (as in config/input-manifest.json) and the ID.
    bytes32 private constant POLICY =
        0x8d9ae1dda2e503550cafade93c54c1b8ecc8eb4b6dab3b843c72a478bb892d2f;
    bytes32 private constant LAYOUT =
        0xa0cce649d992c6f17d1e27c68ac4b900b828ff6ef0bfe8da7c2491fed9f02225;
    bytes32 private constant KL =
        0xb8fb55ed7c70c4cdc7bac01e804dd0dc79349022ba7972957c7e50a29dc974a2;
    bytes32 private constant KEY =
        0x123dc39e8947fd3ba838d7a1a35d587c2f0e1707d1bca9b6ed551b52bf0c2e09;
    bytes32 private constant LEAF0 =
        0xc9484f50fedfaf4e28ec9d1b5d19c3cd5e97bf4582511da49f9eb5693f10e1e0;
    bytes32 private constant ID =
        0x79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183;
    // scripts/recompute-anchor.py over the fixture files; also recomputed from the hashes above.
    bytes32 private constant FIXTURE_DIGEST =
        0x527d75d42538d608c874cc47a0e605b674448dd6ccae18d6279475167e5374a9;

    address private constant A = address(0xA11CE);
    address private constant B = address(0xB0B);

    function setUp() public {
        reg = new ModelCommitmentAnchor();
    }

    function leaves1() private pure returns (bytes32[] memory l) {
        l = new bytes32[](1);
        l[0] = LEAF0;
    }

    function asA() private {
        vm.startPrank(A);
    }

    // --- the digest rule ---

    function test_digest_matches_cross_language_vector() public view {
        assertEq(reg.anchorDigest(POLICY, LAYOUT, KL, KEY, leaves1()), FIXTURE_DIGEST, "vector");
    }

    function test_digest_binds_every_field_and_the_leaf_count() public view {
        bytes32 d = reg.anchorDigest(POLICY, LAYOUT, KL, KEY, leaves1());
        bytes32 x = keccak256("x");
        require(reg.anchorDigest(x, LAYOUT, KL, KEY, leaves1()) != d, "policy");
        require(reg.anchorDigest(POLICY, x, KL, KEY, leaves1()) != d, "layout");
        require(reg.anchorDigest(POLICY, LAYOUT, x, KEY, leaves1()) != d, "kl");
        require(reg.anchorDigest(POLICY, LAYOUT, KL, x, leaves1()) != d, "key");
        bytes32[] memory two = new bytes32[](2);
        two[0] = LEAF0;
        two[1] = LEAF0;
        require(reg.anchorDigest(POLICY, LAYOUT, KL, KEY, two) != d, "leaf count");
        bytes32[] memory none = new bytes32[](0);
        require(reg.anchorDigest(POLICY, LAYOUT, KL, KEY, none) != d, "no leaves");
    }

    function test_digest_is_order_sensitive_for_leaves() public view {
        bytes32[] memory ab = new bytes32[](2);
        ab[0] = LEAF0;
        ab[1] = KEY;
        bytes32[] memory ba = new bytes32[](2);
        ba[0] = KEY;
        ba[1] = LEAF0;
        require(
            reg.anchorDigest(POLICY, LAYOUT, KL, KEY, ab)
                != reg.anchorDigest(POLICY, LAYOUT, KL, KEY, ba),
            "leaf order"
        );
    }

    // --- anchor / revoke ---

    function test_anchor_then_live() public {
        vm.warp(1_000);
        asA();
        reg.anchor(ID, FIXTURE_DIGEST, "ipfs://example");
        vm.stopPrank();
        IModelCommitmentAnchor.Anchor memory a = reg.anchorOf(A, ID);
        assertEq(a.anchorDigest, FIXTURE_DIGEST, "digest stored");
        assertEq(uint256(a.anchoredAt), 1_000, "anchoredAt");
        assertEq(uint256(a.revokedAt), 0, "not revoked");
        assertTrue(reg.isAnchored(A, ID), "anchored");
        assertTrue(reg.isLive(A, ID, FIXTURE_DIGEST), "live");
        assertFalse(reg.isLive(A, ID, keccak256("other bytes")), "a different digest is not live");
    }

    function test_unanchored_is_not_live() public view {
        assertFalse(reg.isAnchored(A, ID), "anchored");
        assertFalse(reg.isLive(A, ID, FIXTURE_DIGEST), "live");
    }

    function test_write_once() public {
        asA();
        reg.anchor(ID, FIXTURE_DIGEST, "");
        vm.expectRevert(bytes("FP-ANC: already anchored"));
        reg.anchor(ID, keccak256("swapped artifacts"), "");
        vm.stopPrank();
        assertTrue(reg.isLive(A, ID, FIXTURE_DIGEST), "the first anchor stands");
    }

    function test_zero_inputs_rejected() public {
        asA();
        vm.expectRevert(bytes("FP-ANC: zero commitment ID"));
        reg.anchor(bytes32(0), FIXTURE_DIGEST, "");
        vm.expectRevert(bytes("FP-ANC: zero digest"));
        reg.anchor(ID, bytes32(0), "");
        vm.stopPrank();
    }

    function test_revoke_is_permanent() public {
        asA();
        reg.anchor(ID, FIXTURE_DIGEST, "");
        reg.revoke(ID, "artifact recalled");
        vm.expectRevert(bytes("FP-ANC: already revoked"));
        reg.revoke(ID, "again");
        vm.expectRevert(bytes("FP-ANC: already anchored"));
        reg.anchor(ID, FIXTURE_DIGEST, "");
        vm.stopPrank();
        assertFalse(reg.isAnchored(A, ID), "revoked is not anchored");
        assertFalse(reg.isLive(A, ID, FIXTURE_DIGEST), "revoked is not live");
    }

    function test_revoke_needs_own_anchor() public {
        asA();
        reg.anchor(ID, FIXTURE_DIGEST, "");
        vm.stopPrank();
        vm.startPrank(B);
        vm.expectRevert(bytes("FP-ANC: not anchored"));
        reg.revoke(ID, "not mine");
        vm.stopPrank();
        assertTrue(reg.isLive(A, ID, FIXTURE_DIGEST), "A's anchor untouched");
    }

    function test_anchorers_are_independent() public {
        asA();
        reg.anchor(ID, FIXTURE_DIGEST, "");
        vm.stopPrank();
        vm.startPrank(B);
        reg.anchor(ID, keccak256("B disagrees"), "");
        reg.revoke(ID, "B withdraws");
        vm.stopPrank();
        assertTrue(reg.isLive(A, ID, FIXTURE_DIGEST), "A unaffected by B");
        assertFalse(reg.isAnchored(B, ID), "B revoked");
    }

    function test_erc165() public view {
        assertTrue(reg.supportsInterface(type(IModelCommitmentAnchor).interfaceId), "anchor");
        assertTrue(reg.supportsInterface(type(IERC165).interfaceId), "erc165");
        assertFalse(reg.supportsInterface(0xffffffff), "bogus");
    }

    // anchorRef: the key of one anchor row (chain + registry + anchorer + commitment ID); the content digest stays chain-free.
    // Cross-language vector: scripts/recompute-anchor.py --ref 84532 0x11..11 0x22..22 0x33..33
    bytes32 constant REF_VECTOR = 0xe6979b5c93b3046f1cf20485a65b525ee395468c2f8c897800ce38899d508cc0;

    function test_anchorRefFor_vector() public view {
        bytes32 id = 0x3333333333333333333333333333333333333333333333333333333333333333;
        assertEq(
            reg.anchorRefFor(84532, 0x1111111111111111111111111111111111111111, 0x2222222222222222222222222222222222222222, id),
            REF_VECTOR, "ref vector"
        );
    }

    function test_anchorRef_is_this_deployment() public view {
        bytes32 id = keccak256("cid");
        assertEq(reg.anchorRef(address(this), id), reg.anchorRefFor(block.chainid, address(reg), address(this), id), "view = rule");
    }

    function test_anchorRef_changes_with_every_input() public view {
        bytes32 id = keccak256("cid");
        bytes32 r = reg.anchorRefFor(1, address(0xA), address(0xB), id);
        assertTrue(reg.anchorRefFor(2, address(0xA), address(0xB), id) != r, "chain");
        assertTrue(reg.anchorRefFor(1, address(0xC), address(0xB), id) != r, "registry");
        assertTrue(reg.anchorRefFor(1, address(0xA), address(0xC), id) != r, "anchorer");
        assertTrue(reg.anchorRefFor(1, address(0xA), address(0xB), keccak256("other")) != r, "commitment");
    }
}
