// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

struct Item { uint256 value; }
struct $attached_to$ { uint256 value; }

library EscapedNames {
    function read($attached_to$ memory self, uint256) internal pure returns (uint256) {
        return self.value;
    }
}

library Locations {
    function append(uint256 self, uint256 value) internal pure returns (uint256) {
        return self * 10 + value;
    }

    function read(Item memory self, uint256) internal pure returns (uint256) {
        return self.value;
    }

    function write(Item memory self, uint256 value) internal pure returns (uint256) {
        self.value = value;
        return self.value;
    }

    function mix(Item memory self, uint256 a, uint256 b) internal pure returns (uint256) {
        return self.value * 100 + a * 10 + b;
    }

    function store(Item storage self, uint256 value) internal returns (Item storage) {
        self.value = value;
        return self;
    }

    function first(uint256[] memory self, uint256) internal pure returns (uint256) {
        return self[0];
    }

    function edit(uint256[] memory self) internal pure returns (uint256) {
        self[0] = 7;
        return self[0];
    }

    function firstByte(bytes memory self, uint256) internal pure returns (uint256) {
        return uint8(self[0]);
    }

    function editByte(bytes memory self) internal pure returns (uint256) {
        self[0] = 0x07;
        return uint8(self[0]);
    }

    function textLength(string memory self) internal pure returns (uint256) {
        return bytes(self).length;
    }
}

contract CallLocations {
    using Locations for Item;
    using Locations for uint256;
    using Locations for uint256[];
    using Locations for bytes;
    using Locations for string;
    using EscapedNames for $attached_to$;

    Item item;
    uint256[] array;
    bytes data;
    string text;
    uint256 receiverCalls;
    $attached_to$ escapedItem;

    function mutateEscaped() internal returns (uint256) { escapedItem.value = 9; return 0; }
    function readEscaped($attached_to$ memory self, uint256) internal pure returns (uint256) {
        return self.value;
    }
    function escapedDirect() external returns (uint256) {
        return EscapedNames.read(escapedItem, mutateEscaped());
    }
    function escapedInternal() external returns (uint256) {
        return readEscaped(escapedItem, mutateEscaped());
    }
    function escapedBound() external returns (uint256) {
        return escapedItem.read(mutateEscaped());
    }

    function mutate() internal returns (uint256) { item.value = 9; return 4; }
    function mutateArray() internal returns (uint256) { array[0] = 9; return 0; }
    function mutateBytes() internal returns (uint256) { data[0] = 0x09; return 0; }
    function readInternal(Item memory self, uint256) internal pure returns (uint256) {
        return self.value;
    }

    function returnItem() internal view returns (Item memory) { return item; }
    function returnArray() internal view returns (uint256[] memory) { return array; }
    function returnBytes() internal view returns (bytes memory) { return data; }
    function returnString() internal view returns (string memory) { return text; }

    function structSites() external view returns (uint256, uint256, uint256, uint256) {
        Item memory p = item;
        Item memory q = Item(0);
        q = item;
        Item memory r = returnItem();
        p.value = 2; q.value = 3; r.value = 4;
        return (p.value, q.value, r.value, item.value);
    }

    function arraySites() external view returns (uint256, uint256, uint256, uint256) {
        uint256[] memory p = array;
        uint256[] memory q = new uint256[](0);
        q = array;
        uint256[] memory r = returnArray();
        p[0] = 2; q[0] = 3; r[0] = 4;
        return (p[0], q[0], r[0], array[0]);
    }

    function bytesSites() external view returns (uint256, uint256, uint256, uint256) {
        bytes memory p = data;
        bytes memory q = hex"";
        q = data;
        bytes memory r = returnBytes();
        p[0] = 0x02; q[0] = 0x03; r[0] = 0x04;
        return (uint8(p[0]), uint8(q[0]), uint8(r[0]), uint8(data[0]));
    }

    function stringSites() external view returns (uint256, uint256, uint256, uint256) {
        string memory p = text;
        string memory q = "";
        q = text;
        string memory r = returnString();
        bytes(p)[0] = 0x61; bytes(q)[0] = 0x62; bytes(r)[0] = 0x63;
        return (uint8(bytes(p)[0]), uint8(bytes(q)[0]), uint8(bytes(r)[0]), uint8(bytes(text)[0]));
    }

    function boundOrder() external returns (uint256) { return item.read(mutate()); }
    function directOrder() external returns (uint256) { return Locations.read(item, mutate()); }
    function internalOrder() external returns (uint256) { return readInternal(item, mutate()); }
    function boundNamed() external returns (uint256) { return item.mix({b: mutate(), a: 3}); }
    function directNamed() external returns (uint256) {
        return Locations.mix({self: item, b: mutate(), a: 3});
    }

    function copy() external view returns (uint256, uint256) {
        uint256 result = item.write(7);
        return (result, item.value);
    }

    function aliasMemory() external pure returns (uint256, uint256) {
        Item memory p = Item(1);
        uint256 result = p.write(7);
        return (result, p.value);
    }

    function reboundScalar() external pure returns (uint256, uint256) {
        uint256 value = 1;
        uint256 result = value.append(value = 9);
        return (result, value);
    }

    function memoryContentMutation() external pure returns (uint256, uint256) {
        Item memory p = Item(1);
        uint256 result = p.read(p.write(9));
        return (result, p.value);
    }

    function reboundMemory() external pure returns (uint256, uint256) {
        Item memory p = Item(1);
        uint256 result = p.read((p = Item(9)).value);
        return (result, p.value);
    }

    function aliasStorage() external returns (uint256) {
        item.store(7).value = 8;
        return item.value;
    }

    function select() internal returns (Item storage) {
        receiverCalls += 1;
        return item;
    }

    function computedReceiver() external returns (uint256, uint256) {
        uint256 result = select().read(mutate());
        return (result, receiverCalls);
    }

    function arrayOrder() external returns (uint256) { return array.first(mutateArray()); }
    function directArrayOrder() external returns (uint256) {
        return Locations.first(array, mutateArray());
    }

    function arrayCopy() external view returns (uint256, uint256) {
        uint256 result = array.edit();
        return (result, array[0]);
    }

    function arrayAlias() external pure returns (uint256, uint256) {
        uint256[] memory p = new uint256[](1);
        p[0] = 1;
        uint256 result = p.edit();
        return (result, p[0]);
    }

    function calldataArray(uint256[] calldata p) external pure returns (uint256, uint256) {
        uint256 result = p.edit();
        return (result, p[0]);
    }

    function bytesOrder() external returns (uint256) { return data.firstByte(mutateBytes()); }
    function directBytesOrder() external returns (uint256) {
        return Locations.firstByte(data, mutateBytes());
    }

    function bytesCopy() external view returns (uint256, uint256) {
        uint256 result = data.editByte();
        return (result, uint8(data[0]));
    }

    function bytesAlias() external pure returns (uint256, uint256) {
        bytes memory p = hex"01";
        uint256 result = p.editByte();
        return (result, uint8(p[0]));
    }

    function calldataBytes(bytes calldata p) external pure returns (uint256, uint256) {
        uint256 result = p.editByte();
        return (result, uint8(p[0]));
    }

    function stringCopy() external view returns (uint256) { return text.textLength(); }
    function calldataString(string calldata p) external pure returns (uint256) {
        return p.textLength();
    }
}
