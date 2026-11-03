// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract StorageBytes {
    bytes private data = hex"0102";
    bytes private other;
    string private text = "token";
    mapping(uint256 => bytes) private items;

    function length() external view returns (uint256) {
        return data.length;
    }

    function byteAt(uint256 i) external view returns (bytes1) {
        return data[i];
    }

    function setByte(uint256 i, bytes1 value) external {
        data[i] = value;
    }

    function setShort() external {
        data = hex"00ff017f80";
    }

    function set31() external {
        data = hex"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e";
    }

    function set32() external {
        data = hex"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
    }

    function set33() external {
        data = hex"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20";
    }

    function clear() external {
        data = hex"";
    }

    function copyStorage() external {
        other = data;
        other[0] = data[1];
    }

    function selfCopy() external {
        data = data;
    }

    function storageAlias(bytes1 value) external {
        bytes storage pointer = data;
        pointer[0] = value;
        pointer = other;
        pointer[0] = value;
    }

    function memoryCopy(bytes1 value) external returns (bytes1, bytes1) {
        bytes memory copy = data;
        copy[0] = value;
        return (data[0], copy[0]);
    }

    function calldataCopy() external {
        data = msg.data;
    }

    function stringStorage(bytes1 value) external returns (uint256, bytes1, bytes1) {
        text = unicode"é\x00x";
        bytes storage pointer = bytes(text);
        pointer[0] = value;
        string memory copy = text;
        bytes(copy)[1] = value;
        return (bytes(text).length, bytes(text)[1], bytes(copy)[1]);
    }

    function mapped(bytes1 value) external returns (bytes1, uint256) {
        items[7] = hex"010203";
        bytes storage pointer = items[7];
        pointer[0] = value;
        return (items[7][0], pointer.length);
    }
}
