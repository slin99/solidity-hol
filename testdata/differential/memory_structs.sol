// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

struct Point {
    uint64 x;
    int32 y;
}

contract MemoryStructs {
    struct Line {
        Point a;
        Point b;
        uint8 tag;
        bytes data;
        uint16[] ws;
        uint8[2] pair;
    }

    struct Two {
        uint64 u;
        uint64 v;
    }

    struct Packed {
        uint8 a;
        uint16 b;
    }

    enum Color { Red, Green }

    struct Paint {
        Color c;
        uint8 n;
    }

    Packed packed;
    Paint paint;
    Line line;
    Line other;
    Packed[] packs;

    function positional(uint64 x, int32 y) public pure returns (uint64, int32) {
        Point memory p = Point(x, y);
        return (p.x, p.y);
    }

    function named(uint64 x, int32 y) public pure returns (uint64, int32) {
        Point memory p = Point({y: y, x: x});
        p.x += 1;
        p.y -= 2;
        return (p.x, p.y);
    }

    function zeroed() public pure returns (uint64, int32, uint8, uint256, uint256, uint8) {
        Line memory l;
        return (l.a.x, l.b.y, l.tag, l.data.length, l.ws.length, l.pair[1]);
    }

    function aliasing(uint64 x) public pure returns (uint64, uint64, uint64) {
        Line memory l;
        l.a = Point(x, 1);
        l.b = l.a;
        l.b.x = x + 5;
        Point memory c = l.a;
        c.x += 1;
        return (l.a.x, l.b.x, c.x);
    }

    function array(uint256 n, uint256 i) public pure returns (uint64, int32, uint256) {
        Point[] memory ps = new Point[](n);
        ps[i].x = 9;
        Point memory q = ps[i];
        q.y = -4;
        return (ps[i].x, ps[i].y, ps.length);
    }

    function order(uint64 a) public pure returns (uint64, uint64) {
        uint64 c = a;
        Two memory t = Two({v: c++, u: c++});
        return (t.u, t.v);
    }

    function toStorage(uint8 a, uint16 b) public returns (uint8, uint16) {
        Packed memory p = Packed(a, b);
        packed = p;
        p.a = 1;
        return (packed.a, packed.b);
    }

    function fromStorage() public view returns (uint8, uint16) {
        Packed memory p = packed;
        return (p.a, p.b);
    }

    function snapshot(uint8 a) public returns (uint8, uint8) {
        Packed memory p = packed;
        packed.a = a;
        return (p.a, packed.a);
    }

    function paintCopy() public view returns (uint8) {
        Paint memory p = paint;
        return p.n;
    }

    function passing(uint64 x) public pure returns (uint64, uint64) {
        Point memory p = Point(x, 0);
        double(p);
        Point memory r = make(p.x);
        return (p.x, r.x);
    }

    function double(Point memory p) internal pure {
        p.x *= 2;
    }

    function make(uint64 x) internal pure returns (Point memory r) {
        r.x = x + 1;
    }

    function withBytes(uint8 t) public pure returns (uint256, uint8, uint16) {
        uint16[] memory ws = new uint16[](2);
        ws[1] = 300;
        uint8[2] memory pr;
        pr[0] = 5;
        Line memory l = Line(Point(1, 2), Point(3, 4), t, "abc", ws, pr);
        return (l.data.length, l.pair[0] + l.tag, l.ws[1]);
    }

    // A conditional joins struct references without allocating: writes
    // through the result reach the chosen operand.
    function scalarJoin(bool c) public pure returns (uint256, uint64, uint64) {
        Point memory a = Point(1, 2);
        Point memory b = Point(3, 4);
        uint256 beforePointer;
        assembly { beforePointer := mload(0x40) }
        Point memory r = c ? a : b;
        uint256 afterPointer;
        assembly { afterPointer := mload(0x40) }
        r.x = 9;
        return (afterPointer - beforePointer, a.x, b.x);
    }

    function tupleJoin(bool c) public pure returns (uint256, uint64, uint64, uint256) {
        Point memory a = Point(1, 2);
        Point memory b = Point(3, 4);
        uint256 beforePointer;
        assembly { beforePointer := mload(0x40) }
        (Point memory r, uint256 tag) = c ? (a, uint256(1)) : (b, uint256(2));
        uint256 afterPointer;
        assembly { afterPointer := mload(0x40) }
        r.x = 9;
        return (afterPointer - beforePointer, a.x, b.x, tag);
    }

    // Whole-struct copies into populated storage: nested structs, bytes and
    // arrays are replaced and their old contents cleared, scalar members are
    // written keeping their slot's other bytes.
    function lineToStorage(uint8 t)
        public
        returns (uint8, int32, uint256, uint256, uint16, uint8)
    {
        uint16[] memory ws = new uint16[](2);
        ws[0] = 1;
        ws[1] = 2;
        uint8[2] memory pr;
        pr[0] = 3;
        pr[1] = 4;
        line = Line(Point(5, -6), Point(7, 8), t, "hi", ws, pr);
        return (line.tag, line.a.y, line.data.length, line.ws.length, line.ws[1], line.pair[1]);
    }

    function lineCopy() public returns (uint256, uint256, uint16) {
        other = line;
        return (other.data.length, other.ws.length, other.ws[2]);
    }

    function lineSelfCopy() public returns (uint256, uint16) {
        line = line;
        return (line.data.length, line.ws[0]);
    }

    function replacePacks(uint8 a) public returns (uint256, uint8, uint16) {
        Packed[] memory m = new Packed[](1);
        m[0] = Packed(a, 2);
        packs = m;
        return (packs.length, packs[0].a, packs[0].b);
    }
}
