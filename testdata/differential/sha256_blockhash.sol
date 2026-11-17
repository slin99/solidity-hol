// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// sha256 calls the precompile at address 2; blockhash reads one of the 256
// blocks before the current one, and is 0 for any other.
contract Sha256Blockhash {
    function digest(bytes memory b) public pure returns (bytes32) {
        return sha256(b);
    }

    function digestCalldata(bytes calldata b) external pure returns (bytes32) {
        return sha256(b);
    }

    function digestPacked(uint256 x, address a) public pure returns (bytes32) {
        return sha256(abi.encodePacked(x, a));
    }

    function digestLiterals() public pure returns (bytes32, bytes32) {
        return (sha256(""), sha256("abc"));
    }

    function hashOf(uint256 n) public view returns (bytes32) {
        return blockhash(n);
    }

    function hashOfNarrow(uint8 n) public view returns (bytes32) {
        return blockhash(n);
    }

    function recent() public view returns (bytes32 previous, bytes32 current) {
        previous = blockhash(block.number - 1);
        current = blockhash(block.number);
    }

    function hashInAssembly(uint256 n) public view returns (bytes32 h) {
        assembly { h := blockhash(n) }
    }
}
