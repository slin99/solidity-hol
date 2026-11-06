// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

enum Level { Low, Mid, High }

library Rounding {
    enum Mode { Floor, Ceil }

    function divide(uint256 a, uint256 b, Mode mode) internal pure returns (uint256) {
        uint256 q = a / b;
        if (mode == Mode.Ceil && q * b < a) {
            return q + 1;
        }
        return q;
    }
}

contract Enums {
    enum Status { Idle, Active, Closed }

    // status, level and small share slot 0.
    Status public status;
    Level private level;
    uint8 private small;
    mapping(address => Status) private statuses;
    Status[] private history;

    function setStatus(Status s) external {
        status = s;
        history.push(s);
    }

    function setLevel(Level l) external returns (Level) {
        level = l;
        small = 7;
        return level;
    }

    function current() external view returns (Status, Level) {
        return (status, level);
    }

    function advance() external returns (Status) {
        status = Status(uint8(status) + 1);
        return status;
    }

    function fromUint(uint256 x) external pure returns (Status) {
        return Status(x);
    }

    function toUint(Status s) external pure returns (uint256) {
        return uint256(s);
    }

    function mark(address a, Status s) external {
        statuses[a] = s;
    }

    function isActive(address a) external view returns (bool) {
        return statuses[a] == Status.Active;
    }

    function compare(Level a, Level b) external pure returns (bool, bool) {
        return (a < b, a == Level.High);
    }

    function ceil(uint256 a, uint256 b) external pure returns (uint256) {
        return Rounding.divide(a, b, Rounding.Mode.Ceil);
    }

    function historyAt(uint256 i) external view returns (Status) {
        return history[i];
    }
}
