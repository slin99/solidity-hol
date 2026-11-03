// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {ERC20} from "./openzeppelin/token/ERC20/ERC20.sol";

// A concrete token over OpenZeppelin's ERC20, unmodified: name and symbol
// set at creation, and a mint to set up balances.
contract OZToken is ERC20 {
    constructor(string memory name_, string memory symbol_) ERC20(name_, symbol_) {}

    function mint(address to, uint256 value) external {
        _mint(to, value);
    }
}
