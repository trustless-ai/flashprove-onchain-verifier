// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {TestBase} from "./utils/TestBase.sol";
import {FlashProvePublicValues} from "../src/libraries/FlashProvePublicValues.sol";

/// @notice A thin external wrapper so the tests can turn a `require` in the library into a
///         catchable failure without cheatcodes.
contract DecoderHarness {
    function decode(
        bytes memory publicValues
    ) external pure returns (FlashProvePublicValues.Values memory) {
        return FlashProvePublicValues.decode(publicValues);
    }
}

contract FlashProvePublicValuesTest is TestBase {
    DecoderHarness private harness;

    bytes32 private constant COMMITMENT_ID = keccak256("commitment");
    bytes32 private constant INPUT = keccak256("input");
    bytes32 private constant RESULT = keccak256("result");

    function setUp() public {
        harness = new DecoderHarness();
    }

    function decodes(bytes memory pv) private view returns (bool) {
        try harness.decode(pv) returns (FlashProvePublicValues.Values memory) {
            return true;
        } catch {
            return false;
        }
    }

    function test_decodes_a_yes_block() public view {
        bytes memory pv = buildPublicValues(1, 0, 0, COMMITMENT_ID, INPUT, RESULT);
        FlashProvePublicValues.Values memory values = harness.decode(pv);
        assertEq(uint256(values.verdict), 1, "verdict");
        assertEq(uint256(values.callStatus), 0, "call status");
        assertEq(uint256(values.resultV1Status), 0, "result status");
        assertEq(values.commitmentId, COMMITMENT_ID, "commitment");
        assertEq(values.inputDigest, INPUT, "input");
        assertEq(values.resultV1Digest, RESULT, "output");
    }

    function test_decodes_status_fields_big_endian() public view {
        bytes memory pv = buildPublicValues(4, 0x0102, 0x03040506, COMMITMENT_ID, INPUT, RESULT);
        FlashProvePublicValues.Values memory values = harness.decode(pv);
        assertEq(uint256(values.callStatus), 0x0102, "call status");
        assertEq(uint256(values.resultV1Status), 0x03040506, "result status");
    }

    function test_rejects_short() public view {
        bytes memory pv = new bytes(127);
        assertFalse(decodes(pv), "short block accepted");
    }

    function test_rejects_bad_magic() public view {
        bytes memory pv = buildPublicValues(1, 0, 0, COMMITMENT_ID, INPUT, RESULT);
        pv[0] = 0x00;
        assertFalse(decodes(pv), "bad magic accepted");
    }

    function test_rejects_bad_version() public view {
        bytes memory pv = buildPublicValues(1, 0, 0, COMMITMENT_ID, INPUT, RESULT);
        pv[5] = 0x02;
        assertFalse(decodes(pv), "bad version accepted");
    }

    function test_rejects_reserved_bytes() public view {
        bytes memory pv = buildPublicValues(1, 0, 0, COMMITMENT_ID, INPUT, RESULT);
        pv[6] = 0x01;
        assertFalse(decodes(pv), "reserved byte 6 accepted");

        pv = buildPublicValues(1, 0, 0, COMMITMENT_ID, INPUT, RESULT);
        pv[9] = 0x01;
        assertFalse(decodes(pv), "reserved byte 9 accepted");

        pv = buildPublicValues(1, 0, 0, COMMITMENT_ID, INPUT, RESULT);
        pv[127] = 0x01;
        assertFalse(decodes(pv), "reserved tail accepted");
    }

    function test_extra_trailing_bytes_are_allowed() public view {
        // The block is at the start; the report and status follow it in the public values.
        bytes memory pv = abi.encodePacked(
            buildPublicValues(1, 0, 0, COMMITMENT_ID, INPUT, RESULT),
            "result-v1 status=0\n",
            hex"00000000"
        );
        assertTrue(decodes(pv), "a block followed by the report was rejected");
    }

    function test_rejects_verdict_zero_and_six() public view {
        bytes memory pv = buildPublicValues(0, 0, 0, COMMITMENT_ID, INPUT, RESULT);
        assertFalse(decodes(pv), "verdict 0 accepted");
        pv = buildPublicValues(6, 0, 0, COMMITMENT_ID, INPUT, RESULT);
        assertFalse(decodes(pv), "verdict 6 accepted");
    }

    function test_accepts_all_five_verdicts() public view {
        for (uint8 code = 1; code <= 5; code++) {
            bytes memory pv = buildPublicValues(code, 0, 0, COMMITMENT_ID, INPUT, RESULT);
            assertTrue(decodes(pv), "a declared verdict was rejected");
        }
    }
}
