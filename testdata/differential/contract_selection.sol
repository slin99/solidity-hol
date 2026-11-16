// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

// Three deployable contracts in one file; the suite selects one by name.
contract SelectionStub {
    function version() external pure returns (uint256) {
        return 1;
    }
}

contract SelectionProxy {
    uint256 public calls;

    function version() external returns (uint256) {
        calls += 1;
        return 2;
    }
}

contract SelectionOther {
    function version() external pure returns (uint256) {
        return 3;
    }
}
