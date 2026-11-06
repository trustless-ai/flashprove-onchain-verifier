// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {TestBase} from "./utils/TestBase.sol";
import {IERC165} from "../src/interfaces/IERC165.sol";
import {IProofVerifier} from "../src/interfaces/IProofVerifier.sol";
import {MockSP1Verifier} from "../src/mocks/MockSP1Verifier.sol";
import {FlashProveVerifier} from "../src/FlashProveVerifier.sol";

contract FlashProveVerifierTest is TestBase {
    MockSP1Verifier private mock;
    FlashProveVerifier private sp1;

    bytes32 private constant VKEY = keccak256("program-vkey");
    bytes32 private constant INPUT = keccak256("input");
    bytes32 private constant RESULT = keccak256("result");
    bytes private constant PLACEHOLDER = "FP-PLACEHOLDER-PROOF";

    function setUp() public {
        mock = new MockSP1Verifier(true);
        mock.setExpectedProgramVKey(VKEY);
        sp1 = new FlashProveVerifier(address(mock));
    }

    function bundle(bytes memory pv) private pure returns (bytes memory) {
        return abi.encode(pv, PLACEHOLDER);
    }

    function metadata() private pure returns (bytes memory) {
        return abi.encode(VKEY);
    }

    function test_accepts_a_valid_bundle() public {
        bytes memory pv = buildPublicValues(1, 0, 0, keccak256("id"), INPUT, RESULT);
        assertTrue(sp1.verify(INPUT, RESULT, metadata(), bundle(pv)), "valid bundle rejected");
    }

    function test_rejects_wrong_input_hash() public {
        bytes memory pv = buildPublicValues(1, 0, 0, keccak256("id"), INPUT, RESULT);
        assertFalse(
            sp1.verify(keccak256("other input"), RESULT, metadata(), bundle(pv)),
            "wrong input hash accepted"
        );
    }

    function test_rejects_wrong_output_hash() public {
        bytes memory pv = buildPublicValues(1, 0, 0, keccak256("id"), INPUT, RESULT);
        assertFalse(
            sp1.verify(INPUT, keccak256("other result"), metadata(), bundle(pv)),
            "wrong output hash accepted"
        );
    }

    function test_rejects_when_the_inner_verifier_rejects() public {
        mock.setAccept(false);
        bytes memory pv = buildPublicValues(1, 0, 0, keccak256("id"), INPUT, RESULT);
        assertFalse(sp1.verify(INPUT, RESULT, metadata(), bundle(pv)), "rejected proof accepted");
    }

    function test_rejects_a_different_program_vkey() public {
        mock.setExpectedProgramVKey(keccak256("another program"));
        bytes memory pv = buildPublicValues(1, 0, 0, keccak256("id"), INPUT, RESULT);
        assertFalse(sp1.verify(INPUT, RESULT, metadata(), bundle(pv)), "wrong vkey accepted");
    }

    function test_rejects_malformed_metadata() public {
        bytes memory pv = buildPublicValues(1, 0, 0, keccak256("id"), INPUT, RESULT);
        assertFalse(sp1.verify(INPUT, RESULT, hex"00", bundle(pv)), "short metadata accepted");
        assertFalse(
            sp1.verify(INPUT, RESULT, abi.encode(VKEY, VKEY), bundle(pv)),
            "long metadata accepted"
        );
    }

    function test_rejects_a_malformed_bundle() public {
        assertFalse(
            sp1.verify(INPUT, RESULT, metadata(), hex"deadbeef"),
            "short bundle accepted"
        );
        assertFalse(
            sp1.verify(INPUT, RESULT, metadata(), new bytes(64)),
            "undecodable bundle accepted"
        );
    }

    function test_rejects_a_bad_public_values_block() public {
        bytes memory pv = buildPublicValues(1, 0, 0, keccak256("id"), INPUT, RESULT);
        pv[0] = 0x00; // magic
        assertFalse(sp1.verify(INPUT, RESULT, metadata(), bundle(pv)), "bad block accepted");
    }

    function test_proof_system_and_profile() public view {
        assertEq(
            keccak256(bytes(sp1.proofSystem())),
            keccak256(bytes("zk/sp1")),
            "proof system"
        );
        bytes32 expected = keccak256(abi.encode("zk/sp1", address(sp1).codehash));
        assertEq(sp1.proofProfile(), expected, "proof profile");
        assertNotZero(sp1.proofProfile(), "empty profile");
    }

    function test_supports_interfaces() public view {
        assertTrue(
            sp1.supportsInterface(type(IProofVerifier).interfaceId),
            "IProofVerifier"
        );
        assertTrue(sp1.supportsInterface(type(IERC165).interfaceId), "IERC165");
        assertFalse(sp1.supportsInterface(0xffffffff), "unknown interface");
    }
}
