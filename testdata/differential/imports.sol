// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Counter, ICounter, Point} from "./imports_base.sol";

// A contract whose base, interface, event and struct come from another file,
// and which calls through the imported interface.
contract Imports is Counter {
    Point internal last;

    function count() external view returns (uint256) {
        return n;
    }

    function bump(uint256 by) public override returns (uint256) {
        last.x = n;
        last.y = by;
        n += 2 * by;
        emit Bumped(n);
        return n;
    }

    function lastSum() external view returns (uint256) {
        return last.x + last.y;
    }

    function countOf(address counter) external view returns (uint256) {
        return ICounter(counter).count();
    }
}
