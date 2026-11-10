// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.37;

contract ConstantConversions {
    uint256[300] arr;

    function addressToUint() external pure returns (uint160) {
        return uint160(address(0));
    }

    function addressToBytes() external pure returns (bytes20) {
        return bytes20(address(0));
    }

    function assignmentToInt() external pure returns (int8, uint8) {
        uint8 x;
        int8 result = int8(x = 200);
        return (result, x);
    }

    function assignmentToBytes() external pure returns (bytes1, uint8) {
        uint8 x;
        bytes1 result = bytes1(x = 1);
        return (result, x);
    }

    function lengthToBytes() external view returns (bytes32) {
        return bytes32(arr.length);
    }

    function lengthToUint8() external view returns (uint8) {
        return uint8(arr.length);
    }
}
