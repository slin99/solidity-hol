// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// block.prevrandao and block.difficulty, which the compiler reads with the
// same PREVRANDAO instruction, and address.code, the account's code copied
// into new memory bytes.
contract EnvironmentCode {
    function randao() public view returns (uint256, uint256) {
        return (block.prevrandao, block.difficulty);
    }

    function code(address target) public view returns (bytes memory) {
        return target.code;
    }

    function codeDigest(address target) public view returns (bytes32, uint256) {
        bytes memory c = target.code;
        return (keccak256(c), c.length);
    }

    function payableCodeDigest(address payable target) public view returns (bytes32) {
        return keccak256(target.code);
    }

    function codeByte(address target, uint256 i) public view returns (bytes1) {
        return target.code[i];
    }

    function codeThenAllocate(address target) public view returns (uint256, bytes memory) {
        bytes memory c = target.code;
        bytes memory d = new bytes(3);
        d[0] = 0x01;
        return (c.length, d);
    }
}
