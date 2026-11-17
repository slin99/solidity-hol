// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

struct Outer {
    Types.Inner inner;
    uint16 tag;
}

library Types {
    struct Inner {
        uint8 a;
        Leaf leaf;
    }

    struct Unused {
        uint8 spare;
    }
}

struct Leaf {
    uint32 v;
}

library Math {
    struct Pair {
        uint128 lo;
        uint128 hi;
    }

    function bump(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }
}

interface IShapes {
    struct Box {
        uint64 w;
        uint64 h;
    }
}

abstract contract Shapes {
    struct Tag {
        uint8 t;
    }
}

contract LibraryStructs {
    Outer outer;
    Math.Pair pair;
    mapping(uint256 => Types.Inner) inners;
    IShapes.Box box;
    Shapes.Tag tag;

    function put(uint8 a, uint32 v, uint16 tag) public returns (uint8, uint32, uint16) {
        outer.inner.a = a;
        outer.inner.leaf.v = v;
        outer.tag = tag;
        return (outer.inner.a, outer.inner.leaf.v, outer.tag);
    }

    function setPair(uint128 lo, uint128 hi) public returns (uint256) {
        pair.lo = lo;
        pair.hi = hi;
        return Math.bump(pair.lo) + pair.hi;
    }

    function setInner(uint256 k, uint8 a) public returns (uint8) {
        inners[k].a = a;
        return inners[k].a;
    }

    function setBox(uint64 w, uint64 h, uint8 t) public returns (uint256) {
        box.w = w;
        box.h = h;
        tag.t = t;
        return uint256(box.w) * box.h + tag.t;
    }
}
