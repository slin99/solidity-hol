// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Concats {
    string public base;
    uint256 public calls;

    function two(string memory a, string memory b) public pure returns (string memory) {
        return string.concat(a, b);
    }

    // As an ERC721 tokenURI joins its base URI and the token id.
    function mixed(string calldata a, string memory b) public view returns (string memory) {
        return string.concat(base, a, "/", b);
    }

    function none() public pure returns (string memory, bytes memory) {
        return (string.concat(), bytes.concat());
    }

    function one(string memory a) public pure returns (string memory) {
        return string.concat(a);
    }

    function nested(string memory a) public pure returns (string memory) {
        return string.concat(string.concat(a, "-"), string.concat("[", a, "]"));
    }

    function joinBytes(bytes memory a, bytes2 b, bytes calldata c) public pure returns (bytes memory) {
        return bytes.concat(a, b, hex"ff", "z", c);
    }

    function next() internal returns (string memory) {
        calls += 1;
        return calls == 1 ? "a" : "b";
    }

    // The arguments are evaluated left to right: "ab".
    function order() public returns (string memory) {
        return string.concat(next(), next());
    }
}
