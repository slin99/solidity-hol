// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IPeer {
    event Pinged(address indexed from);

    function ping(uint256 n) external returns (bool);
}

error Refused(uint256 code);
