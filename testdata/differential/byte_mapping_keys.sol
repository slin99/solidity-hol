// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.37;

contract ByteMappingKeys {
    mapping(bytes => uint256) public executableAt;
    mapping(string => uint8) public names;
    mapping(bytes => mapping(string => int16)) public nested;
    bytes internal saved;

    function write(bytes calldata key, uint256 value) external returns (uint256) {
        executableAt[key] = value;
        return executableAt[key];
    }

    function memoryKey(bytes memory key, uint256 value) external returns (uint256) {
        executableAt[key] = value;
        return executableAt[key];
    }

    function storageKey(bytes calldata key, uint256 value) external returns (uint256) {
        saved = key;
        executableAt[saved] = value;
        return executableAt[key];
    }

    function literalKeys() external returns (uint256, uint256, uint8) {
        executableAt[hex"01"] = 7;
        executableAt[hex"0100"] = 9;
        executableAt[hex""] = 13;
        names["alice"] = 42;
        return (executableAt[hex"01"], executableAt[hex"0100"], names["alice"]);
    }

    function nestedKeys(bytes calldata key, string calldata name) external returns (int16) {
        nested[key][name] = -21;
        return nested[key][name];
    }
}
