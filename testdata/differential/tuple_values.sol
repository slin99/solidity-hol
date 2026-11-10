// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract TupleValues {
    struct Pair { uint16 x; uint16 y; }
    Pair private pair;
    uint256 private trace;
    uint256[2] private data;

    function conditional(bool choose, uint8 value) external pure returns (bool, uint8) {
        return choose ? (true, value) : (false, 0);
    }

    function nested(bool a, bool b) external pure returns (int16, bool) {
        return a ? (b ? (int16(-300), true) : (int16(7), false)) : (int16(0), false);
    }

    function _values(uint256 marker) internal returns (uint16, uint16) {
        trace = marker;
        return (uint16(marker), uint16(marker + 1));
    }

    function lazy(bool choose) external returns (uint16, uint16) {
        return choose ? _values(7) : _values(9);
    }

    function lazyPanic(bool choose, uint256 denominator) external pure returns (uint256, bool) {
        return choose ? (uint256(5), true) : (100 / denominator, false);
    }

    function members(bool choose) external returns (uint16, uint16) {
        (pair.x, pair.y) = choose ? (uint16(300), uint16(400)) : (uint16(8), uint16(9));
        return (pair.x, pair.y);
    }

    function duplicate() external returns (uint16) {
        (pair.x, pair.x) = (3, 4);
        return pair.x;
    }

    function _mark(uint256 value) internal returns (uint256) {
        trace = trace * 10 + value;
        return value;
    }

    function _index(uint256 marker) internal returns (uint256) {
        _mark(marker);
        return 0;
    }

    function schedule() external returns (uint256, uint256) {
        (data[_index(1)], data[_index(2)]) = (_mark(3), _mark(4));
        return (trace, data[0]);
    }

    function captureBeforeWrite() external returns (uint256, uint256) {
        (data[0], data[data[0]]) = (1, 2);
        return (data[0], data[1]);
    }

    function memoryTargets() external pure returns (uint256, uint256) {
        uint256[] memory a = new uint256[](2);
        uint256 i;
        (a[i], a[i = 1]) = (7, 8);
        return (a[0], a[1]);
    }

    function memoryBytes() external pure returns (bytes1, bytes1) {
        bytes memory a = new bytes(2);
        (a[0], a[1]) = (bytes1(0x12), bytes1(0x34));
        return (a[0], a[1]);
    }

    function memoryIndicesBeforeBounds(uint256 zero) external pure {
        uint256[] memory a = new uint256[](1);
        (a[2], a[1 / zero]) = (7, 8);
    }

    function byteIndicesBeforeBounds(uint256 zero) external pure {
        bytes memory a = new bytes(1);
        (a[2], a[1 / zero]) = (bytes1(0x12), bytes1(0x34));
    }

    function storageBoundsBeforeNextIndex(uint256 zero) external {
        (data[zero + 2], data[1 / zero]) = (7, 8);
    }

    function byteCompound() external pure returns (bytes1) {
        bytes memory a = new bytes(1);
        a[0] = 0x12;
        a[0] |= 0x01;
        return a[0];
    }

    function byteArrayCompound() external pure returns (bytes1) {
        bytes1[] memory a = new bytes1[](1);
        a[0] = 0x12;
        a[0] |= 0x01;
        return a[0];
    }

    function hole() external returns (uint16) {
        (, pair.y) = (3, 4);
        return pair.y;
    }

    function snapshots(uint256 value) external pure returns (uint256, uint256) {
        uint256 other = 2;
        (value, other) = (other, value);
        return (value, other);
    }
}
