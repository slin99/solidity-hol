// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// type(T).max and type(T).min of integer types: constants of type T.

contract TypeBounds {
    function bounds()
        external
        pure
        returns (uint8, uint8, int8, int8, uint256, int256, int256)
    {
        return (
            type(uint8).min,
            type(uint8).max,
            type(int8).min,
            type(int8).max,
            type(uint256).max,
            type(int256).min,
            type(int256).max
        );
    }

    // An allowance of type(uint256).max is never decreased.
    function spend(uint256 allowance, uint256 value) external pure returns (uint256) {
        if (allowance != type(uint256).max) {
            allowance -= value;
        }
        return allowance;
    }

    function fitsInt8(int256 x) external pure returns (bool) {
        return x >= type(int8).min && x <= type(int8).max;
    }

    // Widened to uint256 as an operand, so the sum does not overflow uint16.
    function aboveUint16(uint256 x) external pure returns (uint256) {
        return x + type(uint16).max;
    }

    // Arithmetic in the bound's own type: int16 overflow reverts.
    function belowInt16Min(int16 x) external pure returns (int16) {
        return type(int16).min - x;
    }
}
