// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// A fallback taking the whole calldata and returning raw bytes: its result
// is the return data itself, not an ABI encoding.
contract BytesFallback {
    uint256 public calls;

    function ping() external pure returns (uint256) {
        return 7;
    }

    fallback(bytes calldata input) external returns (bytes memory) {
        calls += 1;
        if (input.length > 0 && input[0] == 0xee) {
            return input;
        }
        bytes memory reversed = new bytes(input.length);
        for (uint256 i = 0; i < input.length; i++) {
            reversed[i] = input[input.length - 1 - i];
        }
        return bytes.concat(reversed, bytes1(uint8(input.length)));
    }
}
