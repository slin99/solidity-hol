// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// The peer of the low-level call suite. Called with delegatecall, its code
// runs on the caller's storage, whose slot 0 is the caller's own counter.
contract StaticPeer {
    uint256 private counter;

    function value(uint256 x) external pure returns (uint256) { return x * 2; }
    function nothing() external pure {}
    function fail(uint256 code) external pure { require(code == 0, "peer failed"); }
    function bump() external { counter += 1; }
    function read() external view returns (uint256) { return counter; }
    function bumpThenFail() external { counter += 1; revert("peer failed"); }

    // What the frame it runs in sees.
    function context() external payable returns (address, uint256, address, uint256) {
        return (msg.sender, msg.value, address(this), address(this).balance);
    }

    // A call back into its caller, which writes the caller's storage.
    function reenter() external {
        (bool ok, ) = msg.sender.call(abi.encodeWithSignature("bump()"));
        require(ok, "reentry failed");
    }

    receive() external payable { counter += msg.value; }
}
