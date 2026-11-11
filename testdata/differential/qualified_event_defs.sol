// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

event FreeEvent(uint256 value);

interface IQualifiedEvents {
    event Ordered(uint256 indexed left, uint256 right);
}

library QualifiedLogs {
    event Changed(address indexed actor, uint256 amount);
    event Unused(uint256[][] values);

    function write(uint256 amount) internal {
        emit Changed(msg.sender, amount);
    }
}
