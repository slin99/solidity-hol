// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IToken {
    function transfer(address to, uint256 value) external returns (bool);
    function approve(address spender, uint256 value) external returns (bool);
}

interface IShapes {
    function mixed(uint8 small, int16 wide, bytes4 tag, bool flag) external;
    function withBytes(bytes calldata data, string calldata text, uint256 n) external;
    function one(uint64 x) external;
    function none() external;
    function holder(IToken t) external;
}

contract EncodeCalls {
    IToken public token;
    bytes stored;
    string label;
    uint256 public counter;

    function pay(uint256 x) external {}

    function tick(uint256 x) internal returns (uint256) {
        counter = counter * 10 + x;
        return x;
    }

    function setUp(IToken t, bytes memory b, string memory s) external {
        token = t;
        stored = b;
        label = s;
    }

    // The receiver is a state variable, read without effect.
    function transferCall(address to, uint256 value) external view returns (bytes memory) {
        return abi.encodeCall(token.transfer, (to, value));
    }

    // The receiver is a parameter; the literal becomes a uint256.
    function approveCall(IToken t, address spender) external pure returns (bytes memory) {
        return abi.encodeCall(t.approve, (spender, 5));
    }

    // Each argument converted to its parameter's type.
    function mixedCall(uint8 small, int8 narrow, bytes2 tag) external pure returns (bytes memory) {
        return abi.encodeCall(IShapes.mixed, (small, narrow, tag, true));
    }

    function negativeCall() external pure returns (bytes memory) {
        return abi.encodeCall(IShapes.mixed, (200, -3, bytes4(0), false));
    }

    // Byte sequences from memory and literals, given to calldata parameters.
    function bytesCall(bytes memory data) external pure returns (bytes memory) {
        return abi.encodeCall(IShapes.withBytes, (data, "hi", 7));
    }

    // Byte sequences from storage.
    function storedCall() external view returns (bytes memory) {
        return abi.encodeCall(IShapes.withBytes, (stored, label, 1));
    }

    // One argument, bare or in parentheses.
    function oneCalls(uint64 x) external pure returns (bytes memory, bytes memory) {
        return (abi.encodeCall(IShapes.one, x), abi.encodeCall(IShapes.one, (x + 1)));
    }

    function noneCall() external pure returns (bytes memory) {
        return abi.encodeCall(IShapes.none, ());
    }

    // A contract-typed argument is its address.
    function holderCall() external view returns (bytes memory) {
        return abi.encodeCall(IShapes.holder, (token));
    }

    // this.f names a function of this contract.
    function selfCall() external view returns (bytes memory) {
        return abi.encodeCall(this.pay, (3));
    }

    // The arguments are evaluated in order.
    function orderedCall() external returns (bytes memory, uint256) {
        bytes memory b = abi.encodeCall(IToken.transfer, (address(uint160(tick(1))), tick(2)));
        return (b, counter);
    }
}
