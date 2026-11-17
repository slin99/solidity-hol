// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.37;

interface ITransientValues {
    function enter() external returns (uint256);
    function locked() external view returns (bool);
    function fail() external;
}

abstract contract TransientBase {
    uint8 public persistentBase;
    uint8 transient internal baseTemp;
}

contract TransientValues is TransientBase layout at (6 * 7) {
    uint8 public persistentTail;
    uint8 transient public small;
    int16 transient public signedValue;
    address transient public account;
    bytes4 transient public tag;
    bool transient public locked;
    uint256 transient public wide;
    mapping(uint256 => uint256) public values;

    function roundTrip() external returns (uint8, uint8, int16, address, bytes4, uint256) {
        persistentBase = 3;
        persistentTail = 7;
        baseTemp = 9;
        small = 11;
        signedValue = -19;
        account = address(0x1234);
        tag = 0x12345678;
        wide = 456;
        return (baseTemp, small, signedValue, account, tag, wide);
    }

    function enter() external returns (uint256) {
        require(!locked);
        locked = true;
        return 11;
    }

    function guardRead() external returns (bool) {
        locked = true;
        bool seen = ITransientValues(address(this)).locked();
        locked = false;
        return seen;
    }

    function reenter() external returns (uint256) {
        locked = true;
        return ITransientValues(address(this)).enter();
    }

    function fail() external {
        wide = 999;
        revert();
    }

    function rollback() external returns (uint256) {
        wide = 17;
        try ITransientValues(address(this)).fail() { return 0; }
        catch (bytes memory) { return wide; }
    }

    function layoutMapping(uint256 key, uint256 value) external returns (uint256) {
        values[key] = value;
        return values[key];
    }
}
