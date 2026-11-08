// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Tuples whose components are integer literals, each converted to the type of
// its destination: a return parameter, a declared local, or an assigned one.
contract TupleLiterals {
    function flagged(bool ok) external pure returns (bool, uint8) {
        if (ok) return (true, 6);
        return (false, 0);
    }

    function negative() external pure returns (int8, bool) {
        return (-1, true);
    }

    function fixedBytes() external pure returns (bytes4, uint16) {
        return (0x12345678, 65535);
    }

    function declared() external pure returns (uint8, bool) {
        (uint8 a, bool b) = (7, true);
        return (a, b);
    }

    function assigned(uint256 seed) external pure returns (uint256, int16) {
        uint256 x = seed;
        int16 y;
        (x, y) = (1, -300);
        return (x, y);
    }

    function swapIn(uint256 a) external pure returns (uint256, uint256) {
        uint256 b = 5;
        (a, b) = (b, 9);
        return (a, b);
    }

    function _tryDecimals(uint256 raw) private pure returns (bool ok, uint8 decimals) {
        if (raw <= type(uint8).max) {
            return (true, uint8(raw));
        }
        return (false, 0);
    }

    function decimalsOr18(uint256 raw) external pure returns (uint8) {
        (bool success, uint8 decimals) = _tryDecimals(raw);
        return success ? decimals : 18;
    }
}
