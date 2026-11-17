// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

abstract contract NamespacedStorageBase {
    struct Counter {
        uint64 value;
        bool entered;
    }

    struct Permissions {
        mapping(address => bool) allowed;
    }

    uint256 private constant COUNTER_SLOT = 0x1000;
    uint256 private constant PERMISSIONS_SLOT = 0x2000;

    function counter() internal pure returns (Counter storage item) {
        assembly { item.slot := COUNTER_SLOT }
    }

    function permissions() internal pure returns (Permissions storage item) {
        assembly { item.slot := PERMISSIONS_SLOT }
    }

    function write(Counter storage item, uint64 value, bool entered) internal {
        item.value = value;
        item.entered = entered;
    }
}

contract NamespacedStorage is NamespacedStorageBase {
    function set(uint64 value, bool entered) public returns (uint64, bool) {
        Counter storage item = counter();
        write(item, value, entered);
        return (item.value, item.entered);
    }

    function read() public view returns (uint64, bool) {
        return (counter().value, counter().entered);
    }

    function grant(address who, bool allowed) public returns (bool, uint64) {
        Permissions storage item = permissions();
        item.allowed[who] = allowed;
        return (permissions().allowed[who], counter().value);
    }
}
