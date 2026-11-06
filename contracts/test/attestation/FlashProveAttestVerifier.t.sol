// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {TestBase} from "../utils/TestBase.sol";
import {IERC165} from "../../src/interfaces/IERC165.sol";
import {IProofVerifier} from "../../src/interfaces/IProofVerifier.sol";
import {FlashProveAttestVerifier} from "../../src/attestation/FlashProveAttestVerifier.sol";

/// @notice Interface-level contract tests for the attestation path. They pin what is already
///         final — identifier, profile, ERC-165, guards, constructor validation. The
///         threshold check itself is still a placeholder, and the test that documents that
///         is marked so it gets replaced rather than silently kept once signatures land.
contract FlashProveAttestVerifierTest is TestBase {
    FlashProveAttestVerifier private att;

    bytes32 private constant INPUT = keccak256("input");
    bytes32 private constant RESULT = keccak256("result");

    function committee() private pure returns (address[] memory signers) {
        signers = new address[](3);
        signers[0] = address(0x1001);
        signers[1] = address(0x1002);
        signers[2] = address(0x1003);
    }

    function metadata() private pure returns (bytes memory) {
        return abi.encode(keccak256("committee-v1"));
    }

    function setUp() public {
        att = new FlashProveAttestVerifier(committee(), 2);
    }

    function test_proof_system_and_profile() public view {
        assertEq(keccak256(bytes(att.proofSystem())), keccak256(bytes("attestation/multisig")), "proof system");
        bytes32 expected = keccak256(abi.encode("attestation/multisig", address(att).codehash));
        assertEq(att.proofProfile(), expected, "proof profile");
        assertNotZero(att.proofProfile(), "empty profile");
    }

    function test_supports_interfaces() public view {
        assertTrue(att.supportsInterface(type(IProofVerifier).interfaceId), "IProofVerifier");
        assertTrue(att.supportsInterface(type(IERC165).interfaceId), "IERC165");
        assertFalse(att.supportsInterface(0xffffffff), "unknown interface");
    }

    function test_exposes_the_committee() public view {
        assertEq(att.threshold(), 2, "threshold");
        assertEq(att.signers().length, 3, "committee size");
        assertTrue(att.isSigner(address(0x1001)), "signer 1");
        assertTrue(att.isSigner(address(0x1002)), "signer 2");
        assertTrue(att.isSigner(address(0x1003)), "signer 3");
        assertFalse(att.isSigner(address(0xBEEF)), "outsider");
    }

    function test_rejects_short_metadata() public view {
        assertFalse(
            att.verify(INPUT, RESULT, hex"00", abi.encode(INPUT, RESULT, new bytes(65))),
            "short metadata accepted"
        );
        assertFalse(
            att.verify(INPUT, RESULT, abi.encode(INPUT, RESULT), abi.encode(INPUT, RESULT, new bytes(65))),
            "long metadata accepted"
        );
    }

    function test_rejects_short_proof() public view {
        assertFalse(att.verify(INPUT, RESULT, metadata(), hex"deadbeef"), "short bundle accepted");
    }

    /// @dev Documents the skeleton state: with `_countValidSignatures` returning zero, nothing
    ///      is accepted yet. Replace this test with a real threshold assertion — accepted at
    ///      threshold signatures, rejected one short, duplicates counted once — when the
    ///      signature check lands.
    function test_accepts_nothing_until_the_signature_check_lands() public view {
        assertFalse(
            att.verify(INPUT, RESULT, metadata(), abi.encode(INPUT, RESULT, new bytes(65))),
            "placeholder path accepted a bundle"
        );
    }

    /// @dev The guard is the `abi.encode(bytes, bytes)` minimum (0x80). A bundle between the old
    ///      0x40 floor and that minimum (here 0x60 bytes) is refused at the entry check.
    function test_rejects_proof_between_the_old_floor_and_the_abi_minimum() public view {
        assertFalse(att.verify(INPUT, RESULT, metadata(), new bytes(0x60)), "0x60-byte proof accepted");
    }

    /// @dev Threshold boundary, skeleton state: a 1/1 committee at threshold 1 still answers
    ///      false because `_countValidSignatures` is a placeholder. When the signature check
    ///      lands this becomes the real acceptance assertion for this boundary.
    function test_threshold_one_of_one_placeholder_semantics() public {
        address[] memory one = new address[](1);
        one[0] = address(0x2001);
        FlashProveAttestVerifier solo = new FlashProveAttestVerifier(one, 1);
        assertFalse(
            solo.verify(INPUT, RESULT, metadata(), abi.encode(INPUT, RESULT, new bytes(65))),
            "skeleton accepted a 1/1 bundle"
        );
    }

    /// @dev Threshold boundary, skeleton state: a 3/3 committee at threshold 3 still answers
    ///      false for the same placeholder reason. Replace with the real 3/3 assertion later.
    function test_threshold_three_of_three_placeholder_semantics() public {
        FlashProveAttestVerifier all = new FlashProveAttestVerifier(committee(), 3);
        assertFalse(
            all.verify(INPUT, RESULT, metadata(), abi.encode(INPUT, RESULT, new bytes(65))),
            "skeleton accepted a 3/3 bundle"
        );
    }

    function test_reverts_on_empty_committee() public {
        vm.expectRevert(abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector));
        address[] memory empty = new address[](0);
        new FlashProveAttestVerifier(empty, 1);
    }

    function test_reverts_on_zero_threshold() public {
        vm.expectRevert(abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector));
        new FlashProveAttestVerifier(committee(), 0);
    }

    function test_reverts_on_threshold_above_committee() public {
        vm.expectRevert(abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector));
        new FlashProveAttestVerifier(committee(), 4);
    }

    function test_reverts_on_duplicate_signer() public {
        address[] memory dup = new address[](2);
        dup[0] = address(0x1001);
        dup[1] = address(0x1001);
        vm.expectRevert(abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector));
        new FlashProveAttestVerifier(dup, 1);
    }

    function test_reverts_on_zero_signer() public {
        address[] memory zeroed = new address[](2);
        zeroed[0] = address(0x1001);
        zeroed[1] = address(0);
        vm.expectRevert(abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector));
        new FlashProveAttestVerifier(zeroed, 1);
    }
}
