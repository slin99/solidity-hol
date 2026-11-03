// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// The getters the compiler generates for public state variables: value
// types, packed and inherited; strings and bytes; one key per mapping and one
// index per array, an index past the length reverting with no data.
contract GetterBase {
    uint256 public baseValue;
}

contract PublicGetters is GetterBase {
    uint8 public small;
    bool public flag;
    address public owner;
    int16 public signedValue;
    bytes4 public tag;
    string public name;
    bytes public data;
    mapping(address => uint256) public balances;
    mapping(uint256 => mapping(bool => int8)) public nested;
    uint256[] public list;
    uint16[3] public fixedList;
    uint8[][] public grid;
    mapping(uint256 => string) public labels;
    mapping(bytes4 => uint256[]) public byTag;

    // A function beside the getters, reading what they read.
    function total() public view returns (uint256) {
        return baseValue + small + list.length;
    }
}
