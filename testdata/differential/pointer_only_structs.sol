// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

struct PointerOuter {
    uint128 first;
    uint128 second;
    uint8 head;
    PointerInner inner;
    uint8 tail;
    uint24[11] numbers;
    uint8 afterNumbers;
    mapping(uint256 => uint256) values;
    bytes payload;
    uint8 last;
}

struct PointerInner {
    uint128 x;
    uint256 y;
}

struct PointerAddressSlot {
    address value;
}

contract PointerOnlyStructs {
    // No state declaration reaches these types. Even unused internal
    // procedures must pass the core program's type checks.
    function readOuter(PointerOuter storage item) internal view returns (uint256) {
        return item.inner.y + item.values[0];
    }

    function identity(PointerAddressSlot storage item)
        internal pure returns (PointerAddressSlot storage)
    {
        return item;
    }

    function increment(uint256 x) public pure returns (uint256) {
        return x + 1;
    }
}
