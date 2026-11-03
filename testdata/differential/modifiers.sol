// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Modifiers: invocations in order, arguments over the function's parameters,
// arguments evaluated when their modifier is reached and each converted and
// bound before the next is evaluated, placeholders run zero, one or two times
// with fresh return variables each time, returns in the modifier and in the
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
    bool private active;
    bytes private data;

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

    modifier capture(uint256 seen) {
        total = seen;
        _;
    }

    modifier resetBetween() {
        _;
        active = false;
        _;
    }

    // records the first byte of b, copied from storage before the next
    // argument runs
    modifier firstByte(bytes memory b, uint256 unused) {
        total = uint8(b[0]);
        _;
    }

    // a is bound before the next argument assigns the parameter it reads
    modifier pair(uint256 a, uint256 b) {
        total = a * 10 + b;
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

    function timed() public mark(4) capture(trace) returns (uint256) {
        return total;
    }

    function converted() public firstByte(data, change()) returns (uint256) {
        return total;
    }

    function rebound(uint256 x) public pair(x, x = 2) returns (uint256) {
        return total;
    }

    function change() internal returns (uint256) {
        data = "B";
        return 0;
    }

    function addTwice(uint256 x) public twice returns (uint256) {
        total += x;
        return total;
    }

    function guarded(uint256 x) public onlyOwner atMost(100, x + 1) returns (uint256 r) {
        r = x * 2;
    }

    function fresh() public resetBetween returns (uint256 r) {
        if (active) r = 1;
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
