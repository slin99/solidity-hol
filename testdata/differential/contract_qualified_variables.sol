// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Variables named through the contract declaring them: an immutable read and
// assigned in base constructor arguments, in its initializer and in a
// constructor body, and a state variable and a constant, at creation and at
// runtime.
contract QualifiedBase {
    uint256 immutable fixedValue = QualifiedBase.fixedValue + 1;
    uint256 public stored;
    uint256 public seen;
    uint256 constant K = 7;

    constructor(uint256 x) {
        QualifiedBase.stored = x + QualifiedBase.K;
    }

    function get() external view returns (uint256) {
        return QualifiedBase.fixedValue;
    }
}

contract QualifiedMiddle is QualifiedBase(QualifiedBase.fixedValue += 8) {
    constructor(uint256) {}
}

contract Qualified is QualifiedMiddle {
    constructor() QualifiedMiddle(QualifiedBase.fixedValue += 4) {
        QualifiedBase.seen = QualifiedBase.fixedValue;
    }

    function bump() external returns (uint256) {
        QualifiedBase.stored += 2;
        return QualifiedBase.stored;
    }
}
