// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Storage pointers passed to a base constructor: the derived contract's state
// is written through them before its own constructor body runs.
struct Slot {
    mapping(uint256 => uint256) m;
    uint256 n;
}

abstract contract PointerBase {
    constructor(mapping(uint256 => uint256) storage m, Slot storage s, uint256[] storage xs) {
        m[5] = 20;
        s.m[7] = 3;
        s.n = 4;
        xs.push(9);
    }
}

contract StoragePointerBase is PointerBase {
    mapping(uint256 => uint256) table;
    mapping(uint256 => Slot) slots;
    uint256[] xs;

    constructor() PointerBase(table, slots[1], xs) {
        xs.push(xs.length);
    }

    function read() public view returns (uint256, uint256, uint256, uint256, uint256) {
        return (table[5], slots[1].m[7], slots[1].n, xs[0], xs[1]);
    }
}
