// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.37;

interface Peer {
    function ping() external;
}

contract AbiParenthesizedTypes {
    struct S {
        uint256 a;
        uint256 b;
    }

    enum E { A, B, C }

    type U is uint64;

    function decodeUint(bytes memory data) external pure returns (uint256) {
        return abi.decode(data, (((uint256))));
    }

    function decodeStruct(bytes memory data) external pure returns (uint256, uint256) {
        S memory s = abi.decode(data, (((S))));
        return (s.a, s.b);
    }

    function decodeArray(bytes memory data) external pure returns (uint256) {
        uint256[] memory xs = abi.decode(data, ((uint256)[]));
        return xs.length;
    }

    function decodePair(bytes memory data) external pure returns (uint256, E) {
        return abi.decode(data, ((uint256), ((E))));
    }

    function bounds() external pure returns (uint256, uint8) {
        return (uint256(type((E)).max), type(((uint8))).max);
    }

    function convert(uint256 x) external pure returns (E, uint8, address) {
        return (((E))(x), (uint8)(x), address((Peer)(address(uint160(x)))));
    }

    function wrap(uint64 x) external pure returns (uint64) {
        return U.unwrap(((U)).wrap(x));
    }

    function construct(uint256 x) external pure returns (uint256) {
        return ((S))(x, x + 1).b + (S)({a: x, b: 2}).b;
    }
}
