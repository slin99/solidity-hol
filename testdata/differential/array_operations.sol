// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract ArrayOperations {
    struct Pair {
        uint64 x;
        uint64 y;
    }

    struct Bundle {
        Pair pair;
        bytes data;
        uint16[] values;
        uint8[3] fixedValues;
    }

    struct WithMap {
        uint64 x;
        mapping(uint256 => uint256) extra;
    }

    struct Node {
        uint64 value;
        Node[] children;
    }

    enum Color { Red, Green, Blue }

    Pair[] pairs;
    Bundle[] bundles;
    uint16[][] rows;
    uint8[3][] fixedRows;
    bytes[] blobs;
    string[] names;
    WithMap[] mapped;
    mapping(uint256 => uint256)[] maps;
    Node[] nodes;
    Color[] colors;
    uint8[] small;
    uint256 effects;
    Pair[] otherPairs;
    Color[][] enumRows;
    Pair[][] pairRows;

    function structPush(uint64 x, uint64 y) public returns (uint256, uint64, uint64) {
        pairs.push(Pair(x, y));
        Pair storage p = pairs.push();
        p.x = 9;
        p.y = 10;
        uint256 n = pairs.length;
        uint64 a = pairs[0].x;
        uint64 b = pairs[1].y;
        pairs.pop();
        pairs.pop();
        return (n, a, b);
    }

    function storagePush() public returns (uint64, uint64) {
        pairs.push(Pair(3, 4));
        pairs.push(pairs[0]);
        pairs[0].x = 9;
        uint64 a = pairs[1].x;
        uint64 b = pairs[1].y;
        pairs.pop();
        pairs.pop();
        return (a, b);
    }

    function structCopyPadding() public returns (uint256 word) {
        pairs.push(Pair(3, 4));
        assembly {
            mstore(0, pairs.slot)
            word := sload(keccak256(0, 32))
        }
        pairs.pop();
    }

    function base() internal returns (Pair[] storage) {
        effects = effects * 10 + 1;
        return pairs;
    }

    function argument() internal returns (Pair memory) {
        effects = effects * 10 + 2;
        pairs.push(Pair(1, 2));
        return Pair(3, 4);
    }

    function pushOrder() public returns (uint256, uint256, uint64) {
        base().push(argument());
        uint256 order = effects;
        uint256 n = pairs.length;
        uint64 a = pairs[1].x;
        pairs.pop();
        pairs.pop();
        effects = 0;
        return (order, n, a);
    }

    function rootReboundByArgument() public returns (uint256, uint256, uint64) {
        otherPairs.push(Pair(5, 6));
        Pair[] storage a = pairs;
        a.push((a = otherPairs)[0]);
        uint256 n = pairs.length;
        uint256 m = otherPairs.length;
        uint64 x = pairs[0].x;
        pairs.pop();
        otherPairs.pop();
        return (n, m, x);
    }

    function nestedPush() public returns (uint256, uint16, uint16) {
        rows.push(new uint16[](2));
        rows[0][1] = 7;
        rows.push(rows[0]);
        rows[0][1] = 9;
        uint256 n = rows.length;
        uint16 a = rows[0][1];
        uint16 b = rows[1][1];
        rows.pop();
        rows.pop();
        return (n, a, b);
    }

    function nestedEmptyPush() public returns (uint16, uint16) {
        rows.push().push(5);
        uint16[] storage r = rows.push();
        r.push(6);
        uint16 a = rows[0][0];
        uint16 b = rows[1][0];
        rows.pop();
        rows.pop();
        return (a, b);
    }

    function fixedPush() public returns (uint256, uint8) {
        uint8[3] memory a;
        a[2] = 6;
        fixedRows.push(a);
        uint256 n = fixedRows[0].length;
        uint8 b = fixedRows[0][2];
        fixedRows.pop();
        return (n, b);
    }

    function calldataPush(uint16[] calldata a) external returns (uint256, uint16) {
        rows.push(a);
        uint256 n = rows[0].length;
        uint16 b = rows[0][n - 1];
        rows.pop();
        return (n, b);
    }

    function bytesPush(uint256 n) public returns (uint256, bytes1, uint256) {
        bytes memory a = new bytes(n);
        if (n > 0) a[n - 1] = 0x7f;
        blobs.push(a);
        blobs.push("abc");
        names.push("a string longer than thirty one bytes goes here");
        uint256 size = blobs[0].length;
        bytes1 b = n > 0 ? blobs[0][n - 1] : bytes1(0);
        uint256 named = bytes(names[0]).length;
        names.pop();
        blobs.pop();
        blobs.pop();
        return (size, b, named);
    }

    function bundlePush() public returns (uint64, uint256, uint16, uint8) {
        uint16[] memory a = new uint16[](2);
        a[1] = 300;
        uint8[3] memory f;
        f[2] = 7;
        bundles.push(Bundle(Pair(5, 6), "abcdefghijklmnopqrstuvwxyz0123456789", a, f));
        uint64 x = bundles[0].pair.x;
        uint256 n = bundles[0].data.length;
        uint16 v = bundles[0].values[1];
        uint8 w = bundles[0].fixedValues[2];
        bundles.pop();
        return (x, n, v, w);
    }

    function mappingSurvives() public returns (uint64, uint256) {
        WithMap storage a = mapped.push();
        a.x = 5;
        a.extra[3] = 17;
        mapped.pop();
        WithMap storage b = mapped.push();
        uint64 x = b.x;
        uint256 v = b.extra[3];
        mapped.pop();
        return (x, v);
    }

    function mappingElement() public returns (uint256) {
        maps.push()[9] = 4;
        maps.pop();
        mapping(uint256 => uint256) storage r = maps.push();
        uint256 v = r[9];
        maps.pop();
        return v;
    }

    function recursivePop() public returns (uint256) {
        Node storage r = nodes.push();
        for (uint256 i = 0; i < 9; ++i) {
            r.value = uint64(i + 1);
            r = r.children.push();
        }
        r.value = 10;
        nodes.pop();
        return nodes.length;
    }

    function enumMemory() public returns (uint256, Color, Color) {
        Color[] memory a = new Color[](3);
        a[1] = Color.Blue;
        colors.push(a[1]);
        Color first = a[0];
        Color last = colors[0];
        colors.pop();
        return (a.length, first, last);
    }

    function nestedEnumPush() public returns (Color) {
        Color[] memory a = new Color[](2);
        a[1] = Color.Blue;
        enumRows.push(a);
        Color c = enumRows[0][1];
        enumRows.pop();
        return c;
    }

    function structMemory(uint256 n, uint256 i) public pure returns (uint256, uint64, uint64) {
        Pair[] memory a = new Pair[](n);
        a[i].x = 7;
        return (a.length, a[i].x, a[i].y);
    }

    function nestedStructMemory() public pure returns (uint256, uint256, uint64, uint64) {
        Pair[2][] memory a = new Pair[2][](2);
        a[0][1].x = 8;
        return (a.length, a[0].length, a[0][1].x, a[1][1].x);
    }

    function packedPop() public returns (uint8, uint256) {
        small.push(11);
        small.push(22);
        small.pop();
        uint8 first = small[0];
        uint256 n = small.length;
        small.pop();
        return (first, n);
    }

    function emptyPop() public {
        pairs.pop();
    }

    function structArrayCopyPadding() public returns (uint256 word) {
        Pair[] memory a = new Pair[](1);
        a[0] = Pair(3, 4);
        pairs = a;
        assembly { mstore(0, pairs.slot) word := sload(keccak256(0, 32)) }
        pairs.pop();
    }

    function nestedStructArrayCopyPadding() public returns (uint256 word) {
        Pair[] memory a = new Pair[](1);
        a[0] = Pair(3, 4);
        pairRows.push(a);
        assembly {
            mstore(0, pairRows.slot)
            mstore(0, keccak256(0, 32))
            word := sload(keccak256(0, 32))
        }
        pairRows.pop();
    }


    function emptyNestedCopy() public returns (uint256 n) {
        uint16[] memory a = new uint16[](0);
        rows.push(a);
        n = rows[0].length;
        rows.pop();
    }

    function copyInTuple() public returns (uint256 n, Color first, uint256 x) {
        colors.push(Color.Green);
        colors.push(Color.Blue);
        Color[] memory dest;
        (dest, x) = (colors, 7);
        colors[0] = Color.Red;
        n = dest.length;
        first = dest[0];
        colors.pop();
        colors.pop();
    }

}
