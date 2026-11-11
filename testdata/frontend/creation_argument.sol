// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

contract Base {
    constructor(string memory name) {}
}

contract CreationArgument is Base {
    constructor(bytes memory data) Base(readString(data)) {}

    function readString(bytes memory data) internal pure returns (string memory) {
        return abi.decode(data, (string));
    }

    function value() public pure returns (uint256) {
        return 7;
    }
}
