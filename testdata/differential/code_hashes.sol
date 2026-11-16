// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract CodeHashes {
    uint256 public calls;

    function hash(address target) public view returns (bytes32) {
        return target.codehash;
    }

    function payableHash(address payable target) public view returns (bytes32) {
        return target.codehash;
    }

    function selfHash() public view returns (bytes32) {
        return address(this).codehash;
    }

    function isEmpty(address target) public view returns (bool) {
        return target.codehash == bytes32(0);
    }

    function receiver(address target) internal returns (address) {
        calls += 1;
        return target;
    }

    function once(address target) public returns (bytes32, uint256) {
        bytes32 h = receiver(target).codehash;
        return (h, calls);
    }

    function assemblyHash(address target) public view returns (bytes32 h) {
        assembly {
            h := extcodehash(target)
        }
    }

    // extcodehash reads the low 160 bits of its operand.
    function assemblyWordHash(uint256 target) public view returns (bytes32 h) {
        assembly {
            h := extcodehash(target)
        }
    }
}
