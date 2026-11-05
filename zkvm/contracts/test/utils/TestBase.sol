// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @notice The subset of Foundry's cheatcodes these tests and scripts use. Kept minimal so the
///         project has no third-party Solidity dependency.
interface Vm {
    function expectRevert() external;
    function expectRevert(bytes calldata revertData) external;
    function startPrank(address msgSender) external;
    function stopPrank() external;
    function deal(address account, uint256 newBalance) external;
    function warp(uint256 timestamp) external;
    function startBroadcast(uint256 privateKey) external;
    function stopBroadcast() external;
    function envAddress(string calldata name) external view returns (address);
    function envBool(string calldata name) external view returns (bool);
    function envBytes32(string calldata name) external view returns (bytes32);
    function envString(string calldata name) external view returns (string memory);
    function envUint(string calldata name) external view returns (uint256);
}

abstract contract TestBase {
    Vm internal constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    function assertTrue(bool condition, string memory message) internal pure {
        require(condition, message);
    }

    function assertFalse(bool condition, string memory message) internal pure {
        require(!condition, message);
    }

    function assertEq(bytes32 a, bytes32 b, string memory message) internal pure {
        require(a == b, message);
    }

    function assertEq(uint256 a, uint256 b, string memory message) internal pure {
        require(a == b, message);
    }

    function assertEq(bool a, bool b, string memory message) internal pure {
        require(a == b, message);
    }

    function assertEq(address a, address b, string memory message) internal pure {
        require(a == b, message);
    }

    function assertEq(bytes memory a, bytes memory b, string memory message) internal pure {
        require(keccak256(a) == keccak256(b), message);
    }

    function assertNotZero(bytes32 value, string memory message) internal pure {
        require(value != bytes32(0), message);
    }

    /// @notice A canonical 128-byte FPV1 block, as the guest commits it with `commit_slice`
    ///         (raw bytes, no length prefix).
    function buildPublicValues(
        uint8 verdict,
        uint16 callStatus,
        uint32 resultV1Status,
        bytes32 commitmentId,
        bytes32 inputDigest,
        bytes32 resultV1Digest
    ) internal pure returns (bytes memory pv) {
        pv = new bytes(128);
        pv[0] = 0x46;
        pv[1] = 0x50;
        pv[2] = 0x56;
        pv[3] = 0x31;
        pv[4] = 0x00;
        pv[5] = 0x01;
        pv[8] = bytes1(verdict);
        pv[10] = bytes1(uint8(callStatus >> 8));
        pv[11] = bytes1(uint8(callStatus));
        pv[12] = bytes1(uint8(resultV1Status >> 24));
        pv[13] = bytes1(uint8(resultV1Status >> 16));
        pv[14] = bytes1(uint8(resultV1Status >> 8));
        pv[15] = bytes1(uint8(resultV1Status));
        assembly {
            mstore(add(pv, 0x30), commitmentId)
            mstore(add(pv, 0x50), inputDigest)
            mstore(add(pv, 0x70), resultV1Digest)
        }
    }
}
