// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract StaticPeer {
    uint256 private counter;

    function value(uint256 x) external pure returns (uint256) { return x * 2; }
    function nothing() external pure {}
    function fail(uint256 code) external pure { require(code == 0, "peer failed"); }
    function bump() external { counter += 1; }
    function read() external view returns (uint256) { return counter; }
}
