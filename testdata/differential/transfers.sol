// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.37;

contract Transfers {
    uint256 count;
    receive() external payable {}

    function sendValue(address payable target, uint256 amount) external payable returns (uint256, uint256) {
        count++;
        target.transfer(amount);
        return (address(this).balance, target.balance);
    }

    function receiver(address payable target) internal returns (address payable) {
        count = count * 10 + 1;
        return target;
    }
    function value(uint256 amount) internal returns (uint256) {
        count = count * 10 + 2;
        return amount;
    }
    function ordered(address payable target, uint256 amount) external payable returns (uint256) {
        receiver(target).transfer(value(amount));
        return count;
    }

    function snapshot(address payable target, address payable other) external payable returns (uint256, uint256) {
        target.transfer(uint160(address(target = other)));
        return (target.balance, other.balance);
    }

    function allocationGap(address payable target) external payable returns (uint256 gap) {
        bytes memory first = new bytes(1);
        target.transfer(msg.value);
        bytes memory second = new bytes(1);
        assembly { gap := sub(second, first) }
    }

    function returnDataSizes(address payable first, address payable second)
        external returns (uint256 firstSize, uint256 secondSize)
    {
        first.transfer(0);
        assembly { firstSize := returndatasize() }
        second.transfer(0);
        assembly { secondSize := returndatasize() }
    }

    function laterFailure(address payable target) external payable {
        target.transfer(msg.value);
        revert("later");
    }
}
