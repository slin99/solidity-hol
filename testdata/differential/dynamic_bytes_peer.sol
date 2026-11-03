// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract EchoPeer {
    function raw(uint256 mode) external pure returns (bytes memory) {
        assembly {
            mstore(0, 32)
            switch mode
            case 0 {
                mstore(32, 3)
                mstore(64, shl(232, 0x616263))
                return(0, 67)
            }
            case 1 {
                mstore(32, 3)
                return(0, 64)
            }
            case 4 {
                mstore(32, 0xffffffffffffff00)
                return(0, 64)
            }
            case 3 {
                mstore(32, 0xffffffffffffff40)
                return(0, 64)
            }
            default {
                mstore(32, 0x10000000000000000)
                return(0, 64)
            }
        }
    }

    function echo(bytes calldata data, string calldata text) external pure returns (bytes memory, string memory) {
        return (data, text);
    }

    function afterMutation(bytes calldata data, uint256) external pure returns (bytes memory) {
        return data;
    }
    function rawInput(bytes calldata) external pure returns (bytes memory) {
        return msg.data;
    }
}
