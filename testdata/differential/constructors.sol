// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// A constructor chain with base arguments given on the constructors, and
// initializers with side effects; the most derived constructor is payable. Creation evaluates
// the base arguments, most derived first, then runs each contract's
// initializers and constructor, base first; tick records the order.
contract Root {
    uint256 calls;
    uint256 r = tick(10);
    uint256 root;

    constructor(uint256 x) {
        root = x + tick(1);
    }

    function tick(uint256 k) internal returns (uint256) {
        calls = calls + 1;
        return calls * k;
    }
}

contract Mid is Root {
    uint256 m = tick(100);
    uint256 mid;

    constructor(uint256 y) Root(tick(7)) {
        mid = y + tick(1);
    }
}

contract Top is Mid {
    uint256 top;
    uint256 t = tick(1000);
    uint256 paid = msg.value;

    constructor(uint256 z) payable Mid(tick(z)) {
        top = z + tick(1);
    }
}
