// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

interface IArrayPeer {
    function rev(uint256[] calldata a) external pure returns (uint256[] memory);
}

contract StoragePointers {
    struct Point {
        uint128 x;
        uint128 y;
        uint256 z;
    }

    struct Account {
        uint256 balance;
        mapping(uint256 => uint256) allowance;
        uint8[] tags;
    }

    uint256[] dyn;
    uint256[] other;
    uint8[] small;
    uint256[][] nested;
    mapping(uint256 => uint256) table;
    mapping(uint256 => uint256) otherTable;
    mapping(address => Point) points;
    Point origin;
    Point[3] corners;
    Account acct;

    function pushVia(uint256 n) public returns (uint256, uint256) {
        uint256[] storage p = dyn;
        for (uint256 i = 0; i < n; i++) {
            p.push(i * 2 + 1);
        }
        return (dyn.length, p[p.length - 1]);
    }

    function rebind(bool first, uint256 v) public returns (uint256, uint256) {
        uint256[] storage p = dyn;
        if (!first) {
            p = other;
        }
        p.push(v);
        p[0] = p[0] + 1;
        return (dyn.length, other.length);
    }

    function append(uint256[] storage a, uint256 v) internal returns (uint256) {
        a.push(v);
        return a.length;
    }

    function viaParam(uint256 v) public returns (uint256, uint256, uint256) {
        append(dyn, v);
        uint256 n = append(other, v + 1);
        append(other, v + 2);
        return (dyn[0], other[1], n);
    }

    function pick(bool b) internal view returns (uint256[] storage) {
        if (b) {
            return dyn;
        }
        return other;
    }

    function pickNamed(bool b) internal view returns (uint256[] storage r) {
        r = other;
        if (b) {
            r = dyn;
        }
    }

    function viaReturn(bool b, uint256 v) public returns (uint256, uint256, uint256) {
        uint256[] storage p = pick(b);
        p.push(v);
        uint256[] storage q = pickNamed(!b);
        q.push(v + 1);
        return (dyn[0], other[0], pick(true).length);
    }

    function setIn(mapping(uint256 => uint256) storage m, uint256 k, uint256 v) internal {
        m[k] = v;
    }

    function mappings(bool first, uint256 k, uint256 v) public returns (uint256, uint256) {
        mapping(uint256 => uint256) storage m = table;
        if (!first) {
            m = otherTable;
        }
        m[k] += v;
        setIn(m, k + 1, v * 2);
        return (table[k] + table[k + 1], otherTable[k] + otherTable[k + 1]);
    }

    function structPointer(uint128 a, uint128 b) public returns (uint128, uint128, uint256) {
        Point storage p = origin;
        p.x = a;
        p.y = b;
        p.z = uint256(p.x) + p.y;
        return (origin.x, origin.y, origin.z);
    }

    function bump(Point storage p, uint128 d) internal returns (uint128) {
        p.x += d;
        return p.x;
    }

    function inMapping(address who, uint128 d) public returns (uint128, uint256) {
        Point storage p = points[who];
        p.z = 5;
        uint128 x = bump(p, d);
        bump(points[who], d);
        return (x, points[who].x + points[who].z);
    }

    function corner(uint256 i, uint128 y) public returns (uint128, uint128) {
        Point storage c = corners[i];
        c.y = y;
        Point storage d = corners[(i + 1) % 3];
        d.y = c.y + 1;
        return (corners[i].y, corners[(i + 1) % 3].y);
    }

    function account(uint256 k, uint256 v, uint8 t) public returns (uint256, uint256, uint256) {
        Account storage a = acct;
        a.balance = v;
        a.allowance[k] = v + 1;
        a.tags.push(t);
        a.tags.push(t + 1);
        return (acct.balance, acct.allowance[k], acct.tags.length + acct.tags[1]);
    }

    function row(uint256 i, uint256 v) public returns (uint256, uint256) {
        nested = new uint256[][](2);
        uint256[] storage r = nested[i];
        r.push(v);
        r.push(v + 1);
        return (nested[i].length, nested[i][1]);
    }

    function aliasCopy(uint256 v) public returns (uint256, uint256, uint256) {
        uint256[] storage p = dyn;
        uint256[] storage q = dyn;
        p.push(v);
        q[0] = v + 1;
        uint256[] memory m = p;
        p.push(v + 2);
        other = q;
        return (m.length + m[0], p[0], other.length);
    }

    function packedPop(uint256 n) public returns (uint256, uint8) {
        uint8[] storage s = small;
        for (uint256 i = 0; i < n; i++) {
            s.push(uint8(i + 1));
        }
        s.pop();
        return (small.length, s[s.length - 1]);
    }

    function returnsPointer(uint256 n) public returns (uint256[] memory) {
        uint256[] storage p = dyn;
        for (uint256 i = 0; i < n; i++) {
            p.push(i + 20);
        }
        return p;
    }

    function revPointer(address peer) public returns (uint256, uint256) {
        uint256[] storage p = dyn;
        p.push(1);
        p.push(2);
        uint256[] memory r = IArrayPeer(peer).rev(p);
        return (r.length, r[0]);
    }
}
