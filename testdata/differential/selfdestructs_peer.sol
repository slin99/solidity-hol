// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// The selfdestructs suite's peer: delegatecalled, it destroys the caller's
// account, sending its balance to the transaction's sender.
contract Destroyer {
    fallback() external payable {
        selfdestruct(payable(msg.sender));
    }
}
