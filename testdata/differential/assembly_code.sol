// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// codesize and codecopy read the code of the account the frame runs: the
// contract's own, or a library's when its public function is reached by
// DELEGATECALL, while an internal library function runs in the caller's
// code. extcodecopy reads another account's code.
library CodeLib {
    function ownSize() public view returns (uint256 n) {
        assembly { n := codesize() }
    }

    function ownWord(uint256 offset) public view returns (bytes32 w) {
        assembly {
            let p := mload(0x40)
            codecopy(p, offset, 32)
            w := mload(p)
        }
    }

    function callerSize() internal view returns (uint256 n) {
        assembly { n := codesize() }
    }
}

contract AssemblyCode {
    function size() public view returns (uint256 n) {
        assembly { n := codesize() }
    }

    // a word of the running code, zero past its end
    function word(uint256 offset) public view returns (bytes32 w) {
        assembly {
            let p := mload(0x40)
            codecopy(p, offset, 32)
            w := mload(p)
        }
    }

    function prefix(uint256 n) public view returns (bytes memory b) {
        b = new bytes(n);
        assembly { codecopy(add(b, 32), 0, n) }
    }

    function librarySizes() public view returns (uint256 own, uint256 caller) {
        own = CodeLib.ownSize();
        caller = CodeLib.callerSize();
    }

    function libraryWord(uint256 offset) public view returns (bytes32) {
        return CodeLib.ownWord(offset);
    }

    function peerWord(address a, uint256 offset) public view returns (uint256 n, bytes32 w) {
        assembly {
            n := extcodesize(a)
            extcodecopy(a, 0, offset, 32)
            w := mload(0)
        }
    }

    function peerPrefix(address a, uint256 n) public view returns (bytes memory b) {
        b = new bytes(n);
        assembly { extcodecopy(a, add(b, 32), 0, n) }
    }
}
