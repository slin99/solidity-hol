// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

interface IEnumErrors {
    enum State { Pending, Active, Finished }
    error Unexpected(uint256 id, State current, bytes32 allowed);
}

library EnumErrors {
    error Changed(IEnumErrors.State current, int8 delta, uint8 code);
}

contract EnumErrorCases is IEnumErrors {
    uint256 public changes;

    function unexpected(uint256 id, State current, bytes32 allowed) external pure {
        revert IEnumErrors.Unexpected(id, current, allowed);
    }

    function named(uint256 id, State current) external pure {
        revert Unexpected({allowed: bytes32(uint256(7)), current: current, id: id});
    }

    function changed(uint256 raw) external {
        changes += 1;
        revert EnumErrors.Changed(State(raw), -3, 7);
    }

    function nextState() internal returns (State) {
        changes += 1;
        return State.Finished;
    }

    function effectful() external {
        revert EnumErrors.Changed(nextState(), -3, 7);
    }
}
