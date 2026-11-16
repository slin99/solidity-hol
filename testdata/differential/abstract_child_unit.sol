// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

// A concrete contract followed by an abstract one built on it, in one file:
// the unit's contract is the concrete one.
contract AbstractChildData {
    address public owner;
    uint256 public count;

    function bump() external returns (uint256) {
        count += 1;
        return count;
    }
}

abstract contract AbstractChildLogic is AbstractChildData {
    function claim() public {
        owner = msg.sender;
    }
}
