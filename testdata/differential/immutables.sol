// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Immutables: assigned in constructors and inline initializers, read
// before and after assignment during creation, and read at runtime from
// the deployed code, including by getters and, for one initialized with a
// literal, a pure function.
contract Scaled {
    uint256 public immutable scale;
    uint256 public before;

    constructor(uint256 s) {
        before = scale;
        scale = s;
        scale += 1;
    }
}

contract Immutables is Scaled {
    uint256 public first = 1;
    uint256 immutable offset = first + 10;
    uint256 public second = offset + 20;
    int8 public immutable delta;
    bytes4 public immutable tag;
    address public immutable deployer = msg.sender;
    bool immutable negative;
    uint256 immutable unread;
    uint256 immutable factor = 3;
    uint256 public seen;

    constructor(int8 d, bytes4 t) Scaled(7) {
        delta = d;
        tag = t;
        if (d < 0) {
            negative = true;
        } else {
            negative = false;
        }
        unread = 5;
        seen = scale + offset + unread;
    }

    function total() external view returns (uint256) {
        return scale + offset;
    }

    function scaled(uint256 x) external pure returns (uint256) {
        return x * factor;
    }

    function isNegative() external view returns (bool) {
        return negative;
    }

    function shifted(int8 x) external view returns (int8) {
        return delta + x;
    }
}
