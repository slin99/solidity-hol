// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// The getters of public structs: their values and byte sequences in order,
// mappings and other arrays skipped, under mappings and arrays too.
contract StructGetters {
    enum Side { Left, Right }
    struct Item {
        uint8 a;
        uint16 b;
        bool flag;
        address who;
    }
    struct Blob {
        uint256 n;
        bytes data;
        mapping(uint256 => uint256) skippedMapping;
        uint256[] skippedArray;
        string label;
    }
    struct Tagged {
        Side side;
        bytes4 tag;
    }

    Item public item;
    Blob public blob;
    mapping(uint256 => Item) public items;
    Tagged[] public tagged;
    mapping(address => Tagged[2]) public pairs;

    // A function beside the getters, reading what they read.
    function sum() public view returns (uint256) {
        return item.a + item.b + blob.n + tagged.length;
    }
}
