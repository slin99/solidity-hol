// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

abstract contract GetterDeclarations {
    uint256 public scalar;
    mapping(address owner => uint256) public balanceOf;
    uint16[] public values;
    struct Item { uint256 x; bytes data; uint256[] ignored; }
    Item public item;
    mapping(address owner => mapping(uint256 index => uint256)) public nested;
    bytes public blob;
    uint256 public constant constantValue = 12;
}

abstract contract GetterView is GetterDeclarations {}
