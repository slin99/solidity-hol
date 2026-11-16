// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Inline arrays [e0, ..., ek-1]: a fixed-size memory array of the common
// type of the elements. The compiler allocates the array, then evaluates,
// converts and writes each element in order.
contract InlineArrays {
    struct Pair {
        uint256 a;
        string s;
    }

    uint256 public calls;
    uint8[3] private stored;

    function bump() internal returns (uint256) {
        calls += 1;
        return calls;
    }

    function literals() public pure returns (uint16[3] memory) {
        return [1, 2, 300];
    }

    function mixed(uint8 x) public pure returns (uint16[3] memory) {
        return [x, 256, 3];
    }

    function signed(uint256 i) public pure returns (int256) {
        return [int8(-1), 5, -7][i];
    }

    function sum(uint8 x) public pure returns (uint256 total) {
        uint16[3] memory a = [x, 300, 1];
        for (uint256 i = 0; i < a.length; i++) {
            total += a[i];
        }
    }

    function nested() public pure returns (uint8[2][2] memory) {
        return [[1, 2], [3, 4]];
    }

    function addresses(address a) public view returns (address[2] memory) {
        return [a, address(this)];
    }

    function order() public returns (uint256[3] memory) {
        return [bump(), bump() * 10, bump() * 100];
    }

    function assigns(uint8 x) public pure returns (uint8[3] memory) {
        uint8 y = x;
        return [y, y = 9, y];
    }

    function argument(uint8[3] memory a) internal pure returns (uint256) {
        return uint256(a[0]) * 100 + uint256(a[1]) * 10 + a[2];
    }

    function passed() public pure returns (uint256) {
        return argument([1, 2, 3]);
    }

    function store(uint8 x) public returns (uint8) {
        stored = [x, 2, 255];
        return stored[0] + stored[1];
    }

    function strings(uint256 x) public pure returns (string[2] memory) {
        return ["a", string(abi.encode(x))];
    }

    function structs(uint256 x) public pure returns (Pair[2] memory) {
        return [Pair(x, "p"), Pair(x + 1, string(abi.encodePacked(uint8(x))))];
    }

    function bytesElements(bytes calldata b) public pure returns (bytes[3] memory) {
        return [bytes(b), bytes(""), bytes.concat(b, b)];
    }
}
