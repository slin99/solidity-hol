// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Custom errors: declared at file level and in an interface base, both in an
// imported file, and in the contract, named bare or qualified by the
// interface, and reverted with their selector and ABI-encoded arguments.

import {IVaultErrors, Unauthorized} from "./errors_base.sol";

contract Vault is IVaultErrors {
    error Empty();
    error Odd(int8 value, bool flag, uint8 code);

    mapping(address => uint256) private balances;
    address private owner;

    function withdraw(uint256 amount) external returns (uint256) {
        uint256 balance = balances[msg.sender];
        if (balance < amount) {
            revert IVaultErrors.InsufficientBalance(msg.sender, balance, amount);
        }
        balances[msg.sender] = balance - amount;
        return balances[msg.sender];
    }

    function guarded() external view returns (bool) {
        if (msg.sender != owner) revert Unauthorized(msg.sender);
        return true;
    }

    function nonzero(uint256 x) external pure returns (uint256) {
        if (x == 0) revert Empty();
        return x;
    }

    function odd(int8 value, bool flag) external pure {
        revert Odd(value, !flag, 7);
    }
}
