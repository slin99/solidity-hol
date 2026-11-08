// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract CodeLengths {
    uint256 public calls;

    function size(address target) public view returns (uint256) {
        return target.code.length;
    }

    function payableSize(address payable target) public view returns (uint256) {
        return target.code.length;
    }

    function receiver(address target) internal returns (address) {
        calls += 1;
        return target;
    }

    function once(address target) public returns (uint256, uint256) {
        uint256 length = receiver(target).code.length;
        return (length, calls);
    }
}
