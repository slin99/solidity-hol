// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

contract LiteralBytes {
    bytes16 public constant DIGITS = "0123456789abcdef";
    bytes4 public constant SHORT = "ab";
    bytes4 public constant EMPTY = "";
    bytes4 public constant RAW = hex"80ff";
    bytes4 public constant UTF8 = unicode"é";

    function digit(uint256 i) public pure returns (uint256 result) {
        assembly { result := byte(i, DIGITS) }
    }

    function nested() public pure returns (uint32, bytes8) {
        return (uint32(bytes4("ab")), bytes8(bytes4("ab")));
    }

    function echo(bytes4 b) internal pure returns (bytes4) { return b; }

    function argument() public pure returns (bytes4) { return echo("xy"); }

    function wrapping() public pure returns (bytes16) {
        unchecked { return DIGITS; }
    }
}
