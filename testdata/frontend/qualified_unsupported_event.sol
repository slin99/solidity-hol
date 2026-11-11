// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.37;

struct EventPayload {
    uint256 value;
}

library UnsupportedEvents {
    event Payload(EventPayload item);
}

contract QualifiedUnsupportedEvent {
    function supported() external pure returns (uint256) {
        return 7;
    }

    function emitsUnsupported() external {
        emit UnsupportedEvents.Payload(EventPayload(1));
    }
}
