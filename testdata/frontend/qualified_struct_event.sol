// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.37;

struct EventPayload {
    uint256 value;
}

library StructEvents {
    event Payload(EventPayload item);
}

contract QualifiedStructEvent {
    function supported() external pure returns (uint256) {
        return 7;
    }

    function emitsPayload() external {
        emit StructEvents.Payload(EventPayload(1));
    }
}
