// SPDX-License-Identifier: MIT
pragma solidity ^0.8.37;

library ModifierHelpers {
    function next(uint256 n) internal pure returns (uint256) { return n + 1; }
}

abstract contract ModifierBase {
    uint256 internal trace;

    modifier stamp(uint256 n) virtual {
        trace = trace * 10 + 1;
        _;
        trace = trace * 10 + 1;
    }

    modifier gate(uint256 n) virtual;

    function inherited(uint256 n) public stamp(n) returns (uint256) {
        trace = trace * 10 + 9;
        return trace;
    }

    function bodyless(uint256 n) public gate(n) returns (uint256) {
        return n + trace;
    }
}

abstract contract ModifierMiddle is ModifierBase {
    modifier stamp(uint256 n) virtual override {
        trace = trace * 10 + 2;
        _;
        trace = trace * 10 + 2;
    }

    modifier gate(uint256 n) virtual override;

    function inheritedStatic() public ModifierBase.stamp(0) returns (uint256) {
        trace = trace * 10 + 9;
        return trace;
    }
}

abstract contract ModifierRight is ModifierBase {
    modifier stamp(uint256 n) virtual override {
        trace = trace * 10 + 4;
        _;
        trace = trace * 10 + 4;
    }
}

contract VirtualModifiers is ModifierMiddle, ModifierRight {
    constructor() stamp(4) { trace = trace * 10 + 9; }

    modifier stamp(uint256 digit) override(ModifierMiddle, ModifierRight) {
        trace = trace * 10 + ModifierHelpers.next(digit);
        _;
        trace = trace * 10 + 7;
    }

    modifier gate(uint256 required) override(ModifierBase, ModifierMiddle) {
        require(required == 5);
        trace = 42;
        _;
    }

    function direct(uint256 n) public stamp(n) returns (uint256) {
        trace = trace * 10 + 9;
        return trace;
    }

    function qualifiedMiddle() public ModifierMiddle.stamp(0) returns (uint256) {
        trace = trace * 10 + 9;
        return trace;
    }

    function nested() public stamp(2) stamp(3) returns (uint256) {
        trace = trace * 10 + 9;
        return trace;
    }
}
