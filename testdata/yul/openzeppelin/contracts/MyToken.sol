// SPDX-License-Identifier: MIT
//
// The concrete token behind testdata/yul/expected/openzeppelin-erc20.json: a
// real, unmodified OpenZeppelin Contracts v5.1.0 compiled as it ships, with
// this one contract on top. The tree beside this file is OpenZeppelin's own
// `contracts/` directory at the v5.1.0 tag and is not edited; the artifact
// embeds a second copy of these sources as the compiler saw them, so the
// fixture is readable without this directory.
pragma solidity ^0.8.20;

import {ERC20} from "./token/ERC20/ERC20.sol";
import {Ownable} from "./access/Ownable.sol";

contract MyToken is ERC20, Ownable {
    uint256 public immutable cap;

    constructor(uint256 cap_) ERC20("MyToken", "MYT") Ownable(msg.sender) {
        cap = cap_;
    }

    function mint(address to, uint256 amount) external onlyOwner {
        require(totalSupply() + amount <= cap, "cap");
        _mint(to, amount);
    }
}
