// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

import {FreeEvent, IQualifiedEvents, QualifiedLogs} from "./qualified_event_defs.sol";
import * as Names from "./qualified_event_defs.sol";

contract QualifiedEvents {
    uint256 private ticks;

    function next() internal returns (uint256) {
        return ++ticks;
    }

    function libraryEvent(uint256 amount) public {
        emit QualifiedLogs.Changed(msg.sender, amount);
    }

    function libraryFunction(uint256 amount) public {
        QualifiedLogs.write(amount);
    }

    function namedInterfaceEvent() public {
        emit IQualifiedEvents.Ordered({right: next(), left: next()});
    }

    function moduleEvent(uint256 left, uint256 right) public {
        emit Names.IQualifiedEvents.Ordered(left, right);
    }

    function freeEvent(uint256 value) public {
        emit FreeEvent(value);
    }

    function rolledBack() public {
        emit QualifiedLogs.Changed(msg.sender, next());
        revert();
    }
}
