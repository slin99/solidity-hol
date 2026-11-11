// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// The implementation behind the assembly delegatecall suite's proxy, with the
// proxy's storage layout: add writes slot 0 of whichever account it runs in.
contract DelegatePeer {
    uint256 public total;
    address public impl;

    function add(uint256 amount) external returns (uint256) {
        total += amount;
        require(amount != 1, "peer refused");
        return total;
    }
}
