// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Immutables of enum and internal function type, assigned in the
// constructor. The function immutable is called during creation; the enum
// one is also read at runtime.
contract ImmutableKinds {
    enum Mode {
        Off,
        Low,
        High
    }

    Mode public immutable mode;
    function(uint256) internal pure returns (uint256) immutable op;
    uint256 public created;

    constructor(uint8 m, uint256 x) {
        mode = Mode(m);
        op = mode == Mode.High ? triple : increment;
        created = op(x);
    }

    function increment(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    function triple(uint256 x) internal pure returns (uint256) {
        return 3 * x;
    }

    function isHigh() external view returns (bool) {
        return mode == Mode.High;
    }

    function level() external view returns (uint8) {
        return uint8(mode);
    }
}
