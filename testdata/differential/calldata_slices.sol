// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract CalldataSlices {
    bytes private stored;
    function slice(bytes calldata data, uint256 start, uint256 end) external pure returns (bytes memory) {
        return data[start:end];
    }

    function omitted(bytes calldata data, uint256 index) external pure returns (bytes memory, bytes memory, bytes memory) {
        return (data[:index], data[index:], data[:]);
    }

    function nested(bytes calldata data, uint256 a, uint256 b) external pure returns (bytes memory) {
        return data[a:][1:b];
    }

    function prefix(bytes calldata data, uint256 end) external pure returns (bytes4) {
        return bytes4(data[:end]);
    }

    function conditionalSlice(bytes calldata data, uint256 a, uint256 b, bool selected) external pure returns (bytes4) {
        return selected ? bytes4(data[a:b]) : bytes4(hex"11223344");
    }

    function shortCircuitSlice(bytes calldata data, uint256 a, uint256 b, bool selected) external pure returns (bool) {
        return selected && bytes4(data[a:b]) != bytes4(0);
    }

    function selector() external pure returns (bytes4) {
        return bytes4(msg.data[:4]);
    }

    function word(bytes calldata data) external pure returns (uint256) {
        return abi.decode(data[1:], (uint256));
    }

    function array(uint256[] calldata data, uint256 a, uint256 b) external pure returns (uint256[] memory) {
        return data[a:b];
    }

    function fixedElements(uint256[2][] calldata data, uint256 a, uint256 b) external pure returns (uint256) {
        return data[a:b][0][1];
    }

    function _first(uint256[] calldata data) internal pure returns (uint256) {
        return data[0];
    }

    function passSlice(uint256[] calldata data) external pure returns (uint256) {
        return _first(data[1:]);
    }

    function order(bytes calldata data, uint256 index) external pure returns (bytes memory, uint256) {
        bytes calldata result = data[index:index = 3];
        return (result, index);
    }

    function emptyIndex(bytes calldata data) external pure returns (bytes1) {
        return data[1:1][0];
    }

    function baseBeforeBounds(bytes calldata data, bytes calldata other) external pure returns (bytes memory) {
        return data[0:(data = other).length];
    }

    function fixedFromMemory(bytes memory data) external pure returns (bytes1, bytes32) {
        return (bytes1(data), bytes32(data));
    }

    function fixedFromCalldata(bytes calldata data) external pure returns (bytes32) {
        return bytes32(data);
    }

    function fixedFromStorage() external returns (bytes4) {
        stored = hex"112233";
        return bytes4(stored);
    }


    function decodeWithoutAllocation(bytes calldata data) external pure returns (uint256, uint256, uint256) {
        uint256 beforePointer;
        assembly { beforePointer := mload(0x40) }
        uint256 value = abi.decode(data[1:], (uint256));
        uint256 afterPointer;
        assembly { afterPointer := mload(0x40) }
        return (value, beforePointer, afterPointer);
    }

}
