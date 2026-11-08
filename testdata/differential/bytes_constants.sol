// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Number literals as fixed-size bytes: zero, or hex digits that fill the type.
contract BytesConstants {
    // As OpenZeppelin's AccessControl declares its admin role.
    bytes32 public constant DEFAULT_ADMIN_ROLE = 0x00;
    bytes4 public constant TAG = 0x12345678;
    bytes32 public constant FULL = 0x0102030405060708091011121314151617181920212223242526272829303132;

    mapping(bytes32 => bool) public granted;

    function grant(bytes32 role) public {
        granted[role] = true;
    }

    function grantAdmin() public {
        granted[DEFAULT_ADMIN_ROLE] = true;
    }

    function isAdmin(bytes32 role) public pure returns (bool) {
        return role == DEFAULT_ADMIN_ROLE;
    }

    function isTag(bytes4 x) public pure returns (bool, bool) {
        return (x == TAG, x == 0x12345678);
    }

    function locals() public pure returns (bytes2, bytes32, bytes1, bytes32) {
        bytes2 a = 0x1234;
        bytes32 z = 0;
        bytes1 c = 0xff;
        return (a, z, c, FULL);
    }

    function echo(bytes2 b) internal pure returns (bytes2) {
        return b;
    }

    function argument() public pure returns (bytes2) {
        return echo(0xabcd);
    }

    function zero() public pure returns (bytes4) {
        return 0x00000000;
    }

    function foldedZeros() public pure returns (bytes2, bytes2) {
        bytes2 negated = -0;
        bytes2 difference = 1 - 1;
        return (negated, difference);
    }
}
