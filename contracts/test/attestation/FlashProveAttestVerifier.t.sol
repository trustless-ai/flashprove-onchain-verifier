// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {TestBase} from "../utils/TestBase.sol";
import {IERC165} from "../../src/interfaces/IERC165.sol";
import {IProofVerifier} from "../../src/interfaces/IProofVerifier.sol";
import {FlashProveAttestVerifier} from "../../src/attestation/FlashProveAttestVerifier.sol";

/// @notice Contract tests for the attestation path: identifier, profile, ERC-165, guards,
///         constructor validation, and the k-of-n signature check itself (threshold, distinct
///         signers, binding to input/output/metadata/deployment/chain, malformed input).
contract FlashProveAttestVerifierTest is TestBase {
    FlashProveAttestVerifier private att;

    bytes32 private constant INPUT = keccak256("input");
    bytes32 private constant RESULT = keccak256("result");

    uint256 private constant K1 = 0xA11CE;
    uint256 private constant K2 = 0xB0B;
    uint256 private constant K3 = 0xCA11;
    uint256 private constant OUTSIDER = 0xBAD;

    function committee() private pure returns (address[] memory signers) {
        signers = new address[](3);
        signers[0] = vm.addr(K1);
        signers[1] = vm.addr(K2);
        signers[2] = vm.addr(K3);
    }

    function sig(FlashProveAttestVerifier v, uint256 key, bytes32 input, bytes32 output)
        private
        view
        returns (bytes memory)
    {
        bytes32 digest = v.attestationDigest(input, output, keccak256(metadata()));
        (uint8 sv, bytes32 r, bytes32 s) = vm.sign(key, digest);
        return abi.encodePacked(r, s, sv);
    }

    function bundle(bytes memory a) private pure returns (bytes memory) {
        bytes[] memory s = new bytes[](1);
        s[0] = a;
        return abi.encode(s);
    }

    function bundle(bytes memory a, bytes memory b) private pure returns (bytes memory) {
        bytes[] memory s = new bytes[](2);
        s[0] = a;
        s[1] = b;
        return abi.encode(s);
    }

    function bundle(bytes memory a, bytes memory b, bytes memory c)
        private
        pure
        returns (bytes memory)
    {
        bytes[] memory s = new bytes[](3);
        s[0] = a;
        s[1] = b;
        s[2] = c;
        return abi.encode(s);
    }

    function metadata() private pure returns (bytes memory) {
        return abi.encode(keccak256("committee-v1"));
    }

    function setUp() public {
        att = new FlashProveAttestVerifier(committee(), 2);
    }

    function test_proof_system_and_profile() public view {
        assertEq(
            keccak256(bytes(att.proofSystem())),
            keccak256(bytes("attestation/multisig")),
            "proof system"
        );
        bytes32 expected = keccak256(abi.encode("attestation/multisig", address(att).codehash, keccak256(abi.encode(committee(), uint256(2)))));
        assertEq(att.proofProfile(), expected, "proof profile");
        assertNotZero(att.proofProfile(), "empty profile");
    }

    /// @dev Same code, same threshold, different committee: different profile (the committee is in storage, not in the
    ///      codehash, so it has to be bound explicitly).
    function test_profile_distinguishes_committees_with_the_same_threshold() public {
        address[] memory other = new address[](3);
        other[0] = vm.addr(K1);
        other[1] = vm.addr(K2);
        other[2] = vm.addr(OUTSIDER);
        FlashProveAttestVerifier b = new FlashProveAttestVerifier(other, 2);
        assertTrue(att.proofProfile() != b.proofProfile(), "two committees share a profile");
        FlashProveAttestVerifier same = new FlashProveAttestVerifier(committee(), 2);
        assertEq(att.proofProfile(), same.proofProfile(), "same committee, different profile");
    }

    /// @dev A bundle longer than one signature per committee member is refused before decoding.
    function test_oversized_bundle_refused() public view {
        bytes memory s1 = sig(att, K1, INPUT, RESULT);
        bytes memory s2 = sig(att, K2, INPUT, RESULT);
        bytes[] memory four = new bytes[](4);
        four[0] = s1;
        four[1] = s2;
        four[2] = s1;
        four[3] = s2;
        assertFalse(att.verify(INPUT, RESULT, metadata(), abi.encode(four)), "4 signatures on a 3-member committee accepted");
    }

    function test_supports_interfaces() public view {
        assertTrue(att.supportsInterface(type(IProofVerifier).interfaceId), "IProofVerifier");
        assertTrue(att.supportsInterface(type(IERC165).interfaceId), "IERC165");
        assertFalse(att.supportsInterface(0xffffffff), "unknown interface");
    }

    function test_exposes_the_committee() public view {
        assertEq(att.threshold(), 2, "threshold");
        assertEq(att.signers().length, 3, "committee size");
        assertTrue(att.isSigner(vm.addr(K1)), "signer 1");
        assertTrue(att.isSigner(vm.addr(K2)), "signer 2");
        assertTrue(att.isSigner(vm.addr(K3)), "signer 3");
        assertFalse(att.isSigner(address(0xBEEF)), "outsider");
    }

    function test_rejects_short_metadata() public view {
        assertFalse(
            att.verify(INPUT, RESULT, hex"00", abi.encode(INPUT, RESULT, new bytes(65))),
            "short metadata accepted"
        );
        assertFalse(
            att.verify(
                INPUT, RESULT, abi.encode(INPUT, RESULT), abi.encode(INPUT, RESULT, new bytes(65))
            ),
            "long metadata accepted"
        );
    }

    function test_rejects_short_proof() public view {
        assertFalse(att.verify(INPUT, RESULT, metadata(), hex"deadbeef"), "short bundle accepted");
    }

    /// @dev The threshold itself: 2 of 3 accepted, one short rejected.
    function test_accepts_at_threshold_rejects_one_short() public view {
        bytes memory s1 = sig(att, K1, INPUT, RESULT);
        bytes memory s2 = sig(att, K2, INPUT, RESULT);
        assertTrue(att.verify(INPUT, RESULT, metadata(), bundle(s1, s2)), "2-of-3 rejected");
        assertFalse(att.verify(INPUT, RESULT, metadata(), bundle(s1)), "1-of-3 accepted");
    }

    /// @dev Signer order inside the bundle does not matter, and a third signature beyond the
    ///      threshold is harmless.
    function test_any_order_and_extra_signatures() public view {
        bytes memory s1 = sig(att, K1, INPUT, RESULT);
        bytes memory s2 = sig(att, K2, INPUT, RESULT);
        bytes memory s3 = sig(att, K3, INPUT, RESULT);
        assertTrue(att.verify(INPUT, RESULT, metadata(), bundle(s3, s1)), "reverse order rejected");
        assertTrue(
            att.verify(INPUT, RESULT, metadata(), bundle(s2, s3, s1)), "3-of-3 bundle rejected"
        );
    }

    /// @dev The same member twice counts once.
    function test_duplicates_counted_once() public view {
        bytes memory s1 = sig(att, K1, INPUT, RESULT);
        assertFalse(
            att.verify(INPUT, RESULT, metadata(), bundle(s1, s1)), "duplicate counted twice"
        );
        assertFalse(att.verify(INPUT, RESULT, metadata(), bundle(s1, s1, s1)), "triplicate counted");
    }

    /// @dev A valid signature from outside the committee never counts.
    function test_outsider_ignored() public view {
        bytes memory s1 = sig(att, K1, INPUT, RESULT);
        bytes memory so = sig(att, OUTSIDER, INPUT, RESULT);
        assertFalse(att.verify(INPUT, RESULT, metadata(), bundle(s1, so)), "outsider counted");
    }

    /// @dev Each signature binds the input, the output and the metadata: changing any one of
    ///      them after signing rejects the bundle.
    function test_binds_input_output_and_metadata() public view {
        bytes memory b = bundle(sig(att, K1, INPUT, RESULT), sig(att, K2, INPUT, RESULT));
        assertFalse(att.verify(keccak256("other input"), RESULT, metadata(), b), "input not bound");
        assertFalse(att.verify(INPUT, keccak256("other result"), metadata(), b), "output not bound");
        assertFalse(
            att.verify(INPUT, RESULT, abi.encode(keccak256("committee-v2")), b),
            "metadata not bound"
        );
    }

    /// @dev Signatures for one deployment do not count on another (EIP-712 verifyingContract),
    ///      nor on another chain id.
    function test_bound_to_deployment_and_chain() public {
        FlashProveAttestVerifier other = new FlashProveAttestVerifier(committee(), 2);
        bytes memory b = bundle(sig(att, K1, INPUT, RESULT), sig(att, K2, INPUT, RESULT));
        assertFalse(other.verify(INPUT, RESULT, metadata(), b), "replayed on another deployment");
        vm.chainId(block.chainid + 1);
        assertFalse(att.verify(INPUT, RESULT, metadata(), b), "replayed on another chain");
    }

    /// @dev The malleable high-s twin of a valid signature, a bad v and a wrong length are
    ///      ignored rather than counted or reverted on.
    function test_malformed_signatures_ignored() public view {
        bytes memory s1 = sig(att, K1, INPUT, RESULT);
        bytes memory s2 = sig(att, K2, INPUT, RESULT);
        bytes32 r;
        bytes32 s;
        uint8 v;
        assembly {
            r := mload(add(s2, 0x20))
            s := mload(add(s2, 0x40))
            v := byte(0, mload(add(s2, 0x60)))
        }
        uint256 n = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141;
        bytes memory twin =
            abi.encodePacked(r, bytes32(n - uint256(s)), v == 27 ? uint8(28) : uint8(27));
        assertFalse(att.verify(INPUT, RESULT, metadata(), bundle(s1, twin)), "high-s twin counted");
        bytes memory badV = abi.encodePacked(r, s, uint8(29));
        assertFalse(att.verify(INPUT, RESULT, metadata(), bundle(s1, badV)), "v=29 counted");
        bytes memory short = abi.encodePacked(r, s);
        assertFalse(
            att.verify(INPUT, RESULT, metadata(), bundle(s1, short)), "64-byte signature counted"
        );
    }

    /// @dev An undecodable bundle answers false; it never reverts.
    function test_garbage_bundle_returns_false() public view {
        bytes memory junk = new bytes(0xA0);
        for (uint256 i = 0; i < junk.length; i++) {
            junk[i] = 0xff;
        }
        assertFalse(att.verify(INPUT, RESULT, metadata(), junk), "garbage accepted");
        assertFalse(
            att.verify(INPUT, RESULT, metadata(), abi.encode(INPUT, RESULT, new bytes(65))),
            "non-bundle accepted"
        );
    }

    /// @dev The guard is the `abi.encode(bytes, bytes)` minimum (0x80). A bundle between the old
    ///      0x40 floor and that minimum (here 0x60 bytes) is refused at the entry check.
    function test_rejects_proof_between_the_old_floor_and_the_abi_minimum() public view {
        assertFalse(
            att.verify(INPUT, RESULT, metadata(), new bytes(0x60)), "0x60-byte proof accepted"
        );
    }

    /// @dev Threshold boundaries: 1/1 accepts its one signer, 3/3 needs all three.
    function test_threshold_one_of_one() public {
        address[] memory one = new address[](1);
        one[0] = vm.addr(K1);
        FlashProveAttestVerifier solo = new FlashProveAttestVerifier(one, 1);
        assertTrue(
            solo.verify(INPUT, RESULT, metadata(), bundle(sig(solo, K1, INPUT, RESULT))),
            "1/1 rejected"
        );
        assertFalse(
            solo.verify(INPUT, RESULT, metadata(), bundle(sig(solo, K2, INPUT, RESULT))),
            "1/1 outsider accepted"
        );
    }

    function test_threshold_three_of_three() public {
        FlashProveAttestVerifier all = new FlashProveAttestVerifier(committee(), 3);
        bytes memory s1 = sig(all, K1, INPUT, RESULT);
        bytes memory s2 = sig(all, K2, INPUT, RESULT);
        bytes memory s3 = sig(all, K3, INPUT, RESULT);
        assertTrue(all.verify(INPUT, RESULT, metadata(), bundle(s1, s2, s3)), "3/3 rejected");
        assertFalse(all.verify(INPUT, RESULT, metadata(), bundle(s1, s2)), "3/3 accepted with two");
        assertFalse(
            all.verify(INPUT, RESULT, metadata(), bundle(s1, s2, s2)),
            "3/3 accepted with a duplicate"
        );
    }

    function test_reverts_on_committee_above_max() public {
        address[] memory big = new address[](257);
        for (uint256 i = 0; i < big.length; i++) {
            big[i] = address(uint160(0x10000 + i));
        }
        vm.expectRevert(
            abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector)
        );
        new FlashProveAttestVerifier(big, 1);
    }

    function test_reverts_on_empty_committee() public {
        vm.expectRevert(
            abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector)
        );
        address[] memory empty = new address[](0);
        new FlashProveAttestVerifier(empty, 1);
    }

    function test_reverts_on_zero_threshold() public {
        vm.expectRevert(
            abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector)
        );
        new FlashProveAttestVerifier(committee(), 0);
    }

    function test_reverts_on_threshold_above_committee() public {
        vm.expectRevert(
            abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector)
        );
        new FlashProveAttestVerifier(committee(), 4);
    }

    function test_reverts_on_duplicate_signer() public {
        address[] memory dup = new address[](2);
        dup[0] = address(0x1001);
        dup[1] = address(0x1001);
        vm.expectRevert(
            abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector)
        );
        new FlashProveAttestVerifier(dup, 1);
    }

    function test_reverts_on_zero_signer() public {
        address[] memory zeroed = new address[](2);
        zeroed[0] = address(0x1001);
        zeroed[1] = address(0);
        vm.expectRevert(
            abi.encodeWithSelector(FlashProveAttestVerifier.InvalidConfiguration.selector)
        );
        new FlashProveAttestVerifier(zeroed, 1);
    }
}
