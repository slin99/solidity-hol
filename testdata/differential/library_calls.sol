// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

library Logic {
    struct Box { uint256 x; uint256 y; }
    struct $attached_to$ { uint256 x; }
    event Changed(uint256 value, address sender);

    function add(uint256 x, uint256 y) public pure returns (uint256) {
        return x + y;
    }

    function weird($attached_to$ memory value) external pure returns (uint256) {
        return value.x;
    }

    function receiver(LibraryCalls value) external pure returns (address) {
        return address(value);
    }

    function write(Box storage box, uint256 x) external returns (uint256) {
        box.x = x;
        box.y += 1;
        return box.x + box.y;
    }

    function writeVoid(Box storage box, uint256 x) external {
        box.x = x;
        emit Changed(x, msg.sender);
    }

    function first(Box storage box, Box storage other) external view returns (uint256) {
        return box.x * 100 + other.x;
    }

    function append(uint256[] storage values, uint256 x) external returns (uint256) {
        values.push(x);
        return values.length;
    }

    function put(mapping(uint256 => uint256) storage values, uint256 key, uint256 x)
        external returns (uint256)
    {
        values[key] = x;
        return values[key];
    }

    function sumCopy(uint256[] memory values, uint256 extra) external pure returns (uint256) {
        return values[0] + extra;
    }

    function sum(Box memory box) external pure returns (uint256) {
        return box.x + box.y;
    }

    function make(uint256 x) external pure returns (Box memory) {
        return Box(x, x + 1);
    }

    function echo(bytes memory value) external pure returns (bytes memory) {
        return bytes.concat(value, hex"99");
    }

    function environment() external view returns (address, address, uint256) {
        return (address(this), msg.sender, msg.value);
    }

    function fail(Box storage box) external {
        box.x = 999;
        emit Changed(999, msg.sender);
        revert("library failure");
    }

    function shortReturn() external pure returns (uint256) {
        assembly { return(0, 1) }
    }
}

library OtherLogic {
    function nested(uint256 x) external pure returns (uint256) {
        return Logic.add(x, 20);
    }
}

contract LibraryCalls {
    using Logic for LibraryCalls;
    using Logic for uint256;
    using Logic for Logic.Box;
    using Logic for uint256[];
    using Logic for mapping(uint256 => uint256);

    uint256 private prefix;
    Logic.Box private box;
    Logic.Box private other;
    uint256[] private values;
    mapping(uint256 => uint256) private entries;

    function direct(uint256 x, uint256 y) external pure returns (uint256) {
        return Logic.add(x, y);
    }

    function bound(uint256 x, uint256 y) external pure returns (uint256) {
        return x.add(y);
    }

    function namedStruct(uint256 x) external pure returns (uint256) {
        return Logic.weird(Logic.$attached_to$(x));
    }

    function selfBound() external view returns (address) {
        return this.receiver();
    }

    function named(uint256 x, uint256 y) external pure returns (uint256) {
        return Logic.add({y: y, x: x});
    }

    function boundNamed(uint256 x, uint256 y) external pure returns (uint256) {
        return x.add({y: y});
    }

    function receiverSnapshot() external pure returns (uint256, uint256) {
        uint256 x = 3;
        uint256 result = x.add(x = 7);
        return (result, x);
    }

    function write(uint256 x) external returns (uint256) { return Logic.write(box, x); }
    function boundWrite(uint256 x) external returns (uint256) { return box.write(x); }
    function writeVoid(uint256 x) external { box.writeVoid(x); }

    function pointerSnapshot() external view returns (uint256) {
        Logic.Box storage pointer = box;
        return pointer.first(pointer = other);
    }

    function append(uint256 x) external returns (uint256) { return values.append(x); }
    function put(uint256 key, uint256 x) external returns (uint256) {
        return entries.put(key, x);
    }

    function mutate() private returns (uint256) { values[0] = 90; return 4; }

    function earlyCopy() external returns (uint256) {
        return values.sumCopy(mutate());
    }

    function lateEncoding() external returns (uint256) {
        return Logic.sumCopy(values, mutate());
    }

    function memoryArgument(uint256 x, uint256 y) external pure returns (uint256) {
        return Logic.sum(Logic.Box(x, y));
    }

    function memoryResult(uint256 x) external pure returns (uint256, uint256) {
        Logic.Box memory result = Logic.make(x);
        return (result.x, result.y);
    }

    function echo(bytes memory value) external pure returns (bytes memory) {
        return Logic.echo(value);
    }

    function environment() external payable returns (address, address, uint256) {
        return Logic.environment();
    }

    function nested(uint256 x) external pure returns (uint256) { return OtherLogic.nested(x); }

    function addresses() external pure returns (address, address) {
        return (address(Logic), address(OtherLogic));
    }

    function fail() external { box.fail(); }
    function shortReturn() external pure returns (uint256) { return Logic.shortReturn(); }
}
