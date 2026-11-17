// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract ZeroReset {
    struct Pair { uint8 x; bool y; }
    struct Box { uint8 x; uint[] values; mapping(uint => uint) keep; }
    struct Node { uint8 x; Node[] children; }
    struct MemoryBox { uint x; uint[] values; }
    enum Choice { A, B, C }

    uint8 small;
    uint16 neighbour;
    bool flag;
    uint8[3] fixedValues;
    uint8[] values;
    uint8[][] rows;
    bytes data;
    string text;
    Pair pair;
    Box box;
    mapping(uint => Box) boxes;
    Node node;
    uint effects;
    uint8 transient transientValue;

    function scalarLocal() external pure returns (uint, int, bool, address, bytes2, Choice) {
        uint a = 9; int b = -2; bool c = true;
        address d = address(7); bytes2 e = 0x1234; Choice f = Choice.C;
        delete a; delete b; delete c; delete d; delete e; delete f;
        return (a, b, c, d, e, f);
    }
    function f() internal pure returns (uint) { return 9; }
    function functionLocal() external pure returns (uint) {
        function() internal pure returns (uint) g = f;
        delete g;
        return g();
    }
    function packedScalar() external returns (uint8, uint16, bool) {
        delete small;
        return (small, neighbour, flag);
    }
    function packedBool() external returns (uint8, uint16, bool) {
        delete flag;
        return (small, neighbour, flag);
    }
    function transientScalar() external returns (uint) {
        transientValue = 7; delete transientValue; return transientValue;
    }
    function fixedArray() external returns (uint, uint, uint) {
        delete fixedValues;
        return (fixedValues[0], fixedValues[1], fixedValues[2]);
    }
    function dynamicArray() external returns (uint) { delete values; return values.length; }
    function arrayRegrow() external returns (uint, uint) {
        delete values; values.push(); return (values.length, values[0]);
    }
    function arrayElement(uint i) external returns (uint) { delete values[i]; return values[i]; }
    function nestedArray() external returns (uint) { delete rows; return rows.length; }
    function structValue() external returns (uint, bool) { delete pair; return (pair.x, pair.y); }
    function structField() external returns (uint, bool) { delete pair.x; return (pair.x, pair.y); }
    function structMapping() external returns (uint, uint, uint) {
        delete box; return (box.x, box.values.length, box.keep[7]);
    }
    function mappingValue() external returns (uint, uint, uint) {
        delete boxes[5]; return (boxes[5].x, boxes[5].values.length, boxes[5].keep[7]);
    }
    function recursiveStruct() external returns (uint, uint) {
        delete node; return (node.x, node.children.length);
    }
    function bytesValue() external returns (uint) { delete data; return data.length; }
    function stringValue() external returns (uint) { delete text; return bytes(text).length; }
    function next() internal returns (uint) { effects++; return 0; }
    function effectfulIndex() external returns (uint, uint, uint) {
        delete rows[next()]; return (effects, rows.length, rows[0].length);
    }
    function rollback() external { delete box; revert(); }

    function memoryStruct() external pure returns (uint, uint) {
        MemoryBox memory s = MemoryBox(7, new uint[](1)); MemoryBox memory alias_ = s;
        delete s; return (s.x, alias_.x);
    }
    function memoryStructElement() external pure returns (uint, uint) {
        MemoryBox[] memory a = new MemoryBox[](1); a[0].x = 7;
        MemoryBox memory alias_ = a[0]; delete a[0]; return (a[0].x, alias_.x);
    }
    function memoryArray() external pure returns (uint, uint) {
        uint[2] memory a; a[0] = 7; a[1] = 8; uint[2] memory b = a;
        delete a; return (a[0], b[0]);
    }
    function memoryNestedArray() external pure returns (uint, uint) {
        uint[2][1] memory a; a[0][0] = 7; uint[2] memory b = a[0];
        delete a[0]; return (a[0][0], b[0]);
    }
    function memoryBytes() external pure returns (uint, uint) {
        bytes memory a = hex"ab"; bytes memory b = a;
        delete a; return (a.length, b.length);
    }
    function memoryString() external pure returns (uint, uint) {
        string memory a = "abc"; string memory b = a;
        delete a; return (bytes(a).length, bytes(b).length);
    }
    function memoryField() external pure returns (uint, uint) {
        MemoryBox memory s = MemoryBox(7, new uint[](1)); s.values[0] = 9;
        uint[] memory b = s.values; delete s.values; return (s.values.length, b[0]);
    }
    function memoryScalarElement() external pure returns (uint, uint) {
        uint[] memory a = new uint[](1); a[0] = 7; uint[] memory b = a;
        delete a[0]; return (a[0], b[0]);
    }
    function memoryByteElement() external pure returns (bytes1, bytes1) {
        bytes memory a = hex"ab"; bytes memory b = a;
        delete a[0]; return (a[0], b[0]);
    }
    function memoryScalarField() external pure returns (uint, uint) {
        MemoryBox memory s = MemoryBox(7, new uint[](0)); MemoryBox memory b = s;
        delete s.x; return (s.x, b.x);
    }
    function memoryBounds() external pure { uint[] memory a = new uint[](0); delete a[0]; }
}
