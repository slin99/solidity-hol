// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.37;

contract StorageMemoryPadding {
    bytes stored;
    struct Box { bytes data; }
    Box box;
    bytes[] items;
    string text;

    function word() external view returns (bytes32 r) {
        bytes memory m = stored;
        assembly { r := mload(add(m, 32)) }
    }
    function logical() external view returns (bytes1, uint256) {
        bytes memory m = stored;
        return (m[0], m.length);
    }
    function tailWord() external view returns (bytes32 r) {
        bytes memory m = stored;
        assembly { r := mload(add(m, 64)) }
    }
    function stringWord() external view returns (bytes32 r) {
        string memory s = text;
        bytes memory m = bytes(s);
        assembly { r := mload(add(m, 32)) }
    }
    function structWord() external view returns (bytes32 r) {
        Box memory b = box;
        bytes memory m = b.data;
        assembly { r := mload(add(m, 32)) }
    }
    function arrayWord() external view returns (bytes32 r) {
        bytes[] memory a = items;
        bytes memory m = a[0];
        assembly { r := mload(add(m, 32)) }
    }
    function calldataWord(bytes calldata b) external pure returns (bytes32 r) {
        bytes memory m = b;
        assembly { r := mload(add(m, 32)) }
    }
    function argumentWord(bytes memory m) external pure returns (bytes32 r) {
        assembly { r := mload(add(m, 32)) }
    }
}
