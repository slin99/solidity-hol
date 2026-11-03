// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract MemoryBytes {
    function literal(uint256 i) external pure returns (bytes1) {
        bytes memory data = hex"00ff017f80";
        return data[i];
    }

    function aliasWrite(bytes1 value) external pure returns (bytes1) {
        bytes memory original = hex"010203";
        bytes memory shared = original;
        shared[0] = value;
        return original[0];
    }

    function rebind(bytes1 value) external pure returns (bytes1, bytes1) {
        bytes memory original = hex"010203";
        bytes memory shared = original;
        shared = hex"040506";
        shared[0] = value;
        return (original[0], shared[0]);
    }

    function mutate(bytes memory data, bytes1 value) private pure returns (bytes memory) {
        data[1] = value;
        return data;
    }

    function internalAlias(bytes1 value) external pure returns (bytes1, bytes1) {
        bytes memory original = hex"010203";
        bytes memory result = mutate(original, value);
        return (original[1], result[1]);
    }

    function empty() private pure returns (bytes memory result) {
        bytes memory other = hex"abcd";
        other[0] = other[1];
    }

    function defaultLength() external pure returns (uint256) {
        return empty().length;
    }

    function defaultIndex() external pure returns (bytes1) {
        return empty()[0];
    }

    function stringAlias(bytes1 value) external pure returns (bytes1, uint256, bytes1, bytes1) {
        string memory text = unicode"é\x00x";
        bytes memory data = bytes(text);
        data[0] = value;
        return (bytes(text)[0], data.length, data[1], data[2]);
    }

    function borrow(bytes calldata data) private pure returns (bytes calldata result) {
        result = data;
    }

    function calldataCopy(bytes1 value) external pure returns (bytes1, uint256, bytes1) {
        bytes calldata original = borrow(msg.data);
        string calldata text = string(original);
        bytes memory copy = bytes(text);
        copy[0] = value;
        return (original[0], copy.length, copy[0]);
    }
}
