// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract AbiPeer {
    enum Kind { Low, Mid, High }

    struct Inner {
        uint8 x;
        bytes b;
    }

    struct Outer {
        uint64 a;
        Inner[] items;
        string name;
        Kind k;
    }

    struct Pair {
        uint128 left;
        bool flag;
    }

    function echo(Outer calldata o) external pure returns (Outer memory) {
        return o;
    }

    function make(uint64 a, string calldata name) external pure returns (Outer memory o, Pair memory p) {
        o.a = a;
        o.items = new Inner[](2);
        o.items[1] = Inner(9, bytes(name));
        o.name = name;
        o.k = Kind.Mid;
        p = Pair(a, true);
    }

    function fail(Inner calldata i) external pure returns (Outer memory) {
        require(i.x != 0, "zero");
        revert("always");
    }
}
