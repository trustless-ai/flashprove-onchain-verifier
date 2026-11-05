// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @title FlashProvePublicValues — decoder for the `FPV1` block
/// @notice The guest commits, first, exactly 128 raw bytes with `sp1_zkvm::io::commit_slice`,
///         so the block starts at offset 0 of the SP1 public values. The layout is defined by
///         `zkvm/fp-pv/src/pv.rs`; both sides must agree byte for byte.
///
///         offset size field
///         0      4    magic "FPV1" (0x46 0x50 0x56 0x31)
///         4      2    schema version, big-endian, 1
///         6      2    reserved, zero
///         8      1    verdict (1 YES, 2 WITHIN_LIMITS, 3 NO, 4 NOT_A_VERIFICATION, 5 NOT_CHECKED)
///         9      1    reserved, zero
///         10     2    call status, big-endian
///         12     4    result-v1 status field, big-endian
///         16     32   commitment ID
///         48     32   input digest (SHA-256 of the canonical input bundle)
///         80     32   result-v1 digest (SHA-256 of the line, newline excluded)
///         112    16   reserved, zero
library FlashProvePublicValues {
    uint256 internal constant LENGTH = 128;
    bytes4 internal constant MAGIC = 0x46505631;
    uint16 internal constant SCHEMA_VERSION = 1;

    uint8 internal constant VERDICT_YES = 1;
    uint8 internal constant VERDICT_WITHIN_LIMITS = 2;
    uint8 internal constant VERDICT_NO = 3;
    uint8 internal constant VERDICT_NOT_A_VERIFICATION = 4;
    uint8 internal constant VERDICT_NOT_CHECKED = 5;

    struct Values {
        uint8 verdict;
        uint16 callStatus;
        uint32 resultV1Status;
        bytes32 commitmentId;
        bytes32 inputDigest;
        bytes32 resultV1Digest;
    }

    /// @notice Decodes the block at the start of the SP1 public values.
    /// @dev Reverts on a short block, a wrong magic or version, a non-zero reserved byte, or a
    ///      verdict outside 1..=5. Callers that must return false instead of reverting wrap this
    ///      in a try/catch on an external call.
    function decode(bytes memory publicValues) internal pure returns (Values memory v) {
        require(publicValues.length >= LENGTH, "FP-PV: short");

        bytes32 w0;
        bytes32 commitmentId;
        bytes32 inputDigest;
        bytes32 resultV1Digest;
        bytes32 reserved;
        assembly {
            let p := add(publicValues, 0x20)
            w0 := mload(p)
            commitmentId := mload(add(p, 16))
            inputDigest := mload(add(p, 48))
            resultV1Digest := mload(add(p, 80))
            reserved := mload(add(p, 112))
        }

        require(bytes4(w0) == MAGIC, "FP-PV: magic");
        require(uint16(uint256(w0) >> 208) == SCHEMA_VERSION, "FP-PV: schema version");
        require(uint16(uint256(w0) >> 192) == 0, "FP-PV: reserved");
        v.verdict = uint8(uint256(w0) >> 184);
        require(
            v.verdict >= VERDICT_YES && v.verdict <= VERDICT_NOT_CHECKED,
            "FP-PV: verdict code"
        );
        require(uint8(uint256(w0) >> 176) == 0, "FP-PV: reserved");
        v.callStatus = uint16(uint256(w0) >> 160);
        v.resultV1Status = uint32(uint256(w0) >> 128);
        // Only the block's last 16 bytes (offsets 112..128) are reserved; the 16 bytes after
        // them belong to the report, so mask the low half of the loaded word.
        require(uint256(reserved) >> 128 == 0, "FP-PV: reserved");

        v.commitmentId = commitmentId;
        v.inputDigest = inputDigest;
        v.resultV1Digest = resultV1Digest;
    }
}
