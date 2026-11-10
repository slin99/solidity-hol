// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Ecrecovers {
    address public signer;
    uint256 public calls;

    function recover(bytes32 h, uint8 v, bytes32 r, bytes32 s) public pure returns (address) {
        return ecrecover(h, v, r, s);
    }

    // As a permit checks a signature: recovered, compared and kept.
    function check(bytes32 h, uint8 v, bytes32 r, bytes32 s, address owner) public returns (bool) {
        address recovered = ecrecover(h, v, r, s);
        require(recovered != address(0) && recovered == owner, "invalid signature");
        signer = recovered;
        return true;
    }

    function literalV(bytes32 h, bytes32 r, bytes32 s) public pure returns (address, address) {
        return (ecrecover(h, 27, r, s), ecrecover(h, 28, r, s));
    }

    function next() internal returns (uint256) {
        calls += 1;
        return calls;
    }

    // The arguments are evaluated left to right: hash 1 and v 28.
    function order(bytes32 r, bytes32 s) public returns (address, uint256) {
        address a = ecrecover(bytes32(next()), uint8(next() + 26), r, s);
        return (a, calls);
    }
}
