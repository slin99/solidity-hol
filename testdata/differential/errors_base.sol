// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// The errors errors.sol imports: one at file level, one in an interface.

error Unauthorized(address caller);

interface IVaultErrors {
    error InsufficientBalance(address account, uint256 balance, uint256 needed);
}
