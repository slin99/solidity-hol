// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Creation accepts value only when the most derived contract's own
// constructor is payable; a payable base constructor does not make it so.
// The base's argument is given in the inheritance list.
contract PayableBase {
    uint256 paid;

    constructor(uint256 k) payable {
        paid = msg.value + k;
    }
}

contract Plain is PayableBase(1) {}
