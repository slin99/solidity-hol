// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Modifiers: invocations in order, arguments over the function's parameters,
// placeholders run zero, one or two times, returns in the modifier and in the
// body, an inherited modifier, and a constructor modifier.

contract ModifierBase {
    uint256 internal trace;
    address internal owner;

    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    // records k before and after the rest of the function
    modifier mark(uint256 k) {
        trace = trace * 10 + k;
        _;
        trace = trace * 10 + k;
    }
}

contract Modifiers is ModifierBase {
    uint256 private total;

    error TooLarge(uint256 value);

    constructor(uint256 start) mark(start) {
        owner = msg.sender;
        total = start;
    }

    modifier atMost(uint256 limit, uint256 value) {
        if (value > limit) revert TooLarge(value);
        _;
    }

    modifier twice() {
        _;
        _;
    }

    modifier skipIfZero(uint256 v) {
        if (v == 0) return;
        _;
    }

    modifier bumpAfter() {
        _;
        total += 1;
    }

    function ordered(uint256 x) public mark(1) mark(2) returns (uint256) {
        trace = trace * 10 + x;
        return trace;
    }

    function addTwice(uint256 x) public twice returns (uint256) {
        total += x;
        return total;
    }

    function guarded(uint256 x) public onlyOwner atMost(100, x + 1) returns (uint256 r) {
        r = x * 2;
    }

    function skipped(uint256 v) public skipIfZero(v) returns (uint256 r, bool ok) {
        r = v + 1;
        ok = true;
    }

    function early(uint256 v) public bumpAfter returns (uint256) {
        if (v > 5) return v;
        total = v;
        return 0;
    }

    function echo(bytes memory b) public mark(3) returns (bytes memory) {
        return b;
    }

    function state() public view returns (uint256, uint256) {
        return (trace, total);
    }
}
