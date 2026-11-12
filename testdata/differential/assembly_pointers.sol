// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Storage pointer locals in inline assembly: StorageSlot-style getters that
// set a returned pointer's slot, an ERC-7201 namespaced struct reached
// through a constant slot, x.slot and x.offset of pointers to a mapping
// entry, an array field and a bytes value, and a pointer moved to another
// slot and then written through. The slot structs are declared at file
// level; OpenZeppelin's StorageSlot declares them in its library.
struct AddressSlot {
    address value;
}

struct Uint256Slot {
    uint256 value;
}

struct BytesSlot {
    bytes value;
}

library Slots {
    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
        assembly {
            r.slot := slot
        }
    }

    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        assembly {
            r.slot := slot
        }
    }

    function getBytesSlot(bytes32 slot) internal pure returns (BytesSlot storage r) {
        assembly {
            r.slot := slot
        }
    }
}

contract AssemblyPointers {
    struct Entry {
        uint128 a;
        uint128 b;
        uint256[] list;
    }

    /// @custom:storage-location erc7201:example.main
    struct MainStorage {
        uint256 counter;
        mapping(address => uint256) balances;
    }

    // keccak256(abi.encode(uint256(keccak256("example.main")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant MAIN =
        0x183a6125c38840424c4a85fa12bab2ab606c4b6d0e7cc73c0c06ba5300eab500;

    uint256 first;
    mapping(uint256 => Entry) entries;
    bytes data;

    function _main() private pure returns (MainStorage storage $) {
        assembly {
            $.slot := MAIN
        }
    }

    function setOwner(address a) public {
        Slots.getAddressSlot(bytes32(uint256(100))).value = a;
    }

    function owner() public view returns (address) {
        return Slots.getAddressSlot(bytes32(uint256(100))).value;
    }

    function addAt(uint256 slot, uint256 v) public returns (uint256) {
        Uint256Slot storage s = Slots.getUint256Slot(bytes32(slot));
        s.value += v;
        return s.value;
    }

    function bytesAt(uint256 slot) public returns (uint256) {
        Slots.getBytesSlot(bytes32(slot)).value = "pointer";
        return Slots.getBytesSlot(bytes32(slot)).value.length;
    }

    function bumpCounter(uint256 by) public returns (uint256) {
        MainStorage storage $ = _main();
        $.counter += by;
        return $.counter;
    }

    function deposit(address who, uint256 v) public returns (uint256) {
        MainStorage storage $ = _main();
        $.balances[who] += v;
        return $.balances[who];
    }

    function locations(uint256 k) public view
        returns (uint256 s, uint256 o, uint256 ls, uint256 ds)
    {
        Entry storage e = entries[k];
        uint256[] storage l = e.list;
        bytes storage d = data;
        assembly {
            s := e.slot
            o := e.offset
            ls := l.slot
            ds := d.slot
        }
    }

    function repoint(uint256 slot, uint128 v) public returns (uint128 a, uint128 b) {
        Entry storage e = entries[0];
        assembly {
            function moved(t) -> u {
                u := t
            }
            e.slot := moved(slot)
        }
        e.b = v;
        return (e.a, e.b);
    }
}
