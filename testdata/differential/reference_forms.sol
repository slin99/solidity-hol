// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// A library's public function called internally from the library itself.
library Fees {
    function total(uint256 a, uint256 b) public pure returns (uint256) {
        return a + b;
    }

    function twice(uint256 a) internal pure returns (uint256) {
        return total(a, a) + 1;
    }
}

// Parenthesised locations and destinations, conditionals over storage,
// calldata and tuple types, and push and pop of storage bytes.
contract ReferenceForms {
    struct Details {
        uint256 nonce;
        uint256 count;
    }

    struct Part {
        bytes part;
        uint256 tag;
    }

    mapping(address => mapping(address => bool)) operators;
    Details stored;
    Details other;
    bytes data;
    Part state;

    function setOperator(address owner, address operator, bool allowed) external {
        (operators[owner])[operator] = allowed;
    }

    function isOperator(address owner, address operator) external view returns (bool) {
        return (operators[owner])[operator];
    }

    function bumpMemory(uint256 n) external pure returns (uint256, uint256, uint256) {
        Details memory d = Details(n, 0);
        uint256 r = ++(d.nonce);
        (d.count) = 7;
        (d.count) += 1;
        return (r, d.nonce, d.count);
    }

    function bumpStorage() external returns (uint256, uint256) {
        uint256 r = (stored.nonce)++;
        delete (other.count);
        return (r, stored.nonce);
    }

    function pick(bool first, uint256 by) external returns (uint256, uint256) {
        Details storage d = first ? stored : other;
        d.count += by;
        return (stored.count, other.count);
    }

    function pickPair(bool first) external returns (uint256, uint256) {
        (Details storage d, uint256 k) = first ? (stored, 1) : (other, 2);
        d.nonce = k;
        return (stored.nonce, other.nonce);
    }

    function head(bool whole, bytes calldata b) external pure returns (bytes memory) {
        return whole ? b : b[:1];
    }

    function pushBytes(bytes calldata b) external returns (bytes memory) {
        for (uint256 i = 0; i < b.length; i++) {
            state.part.push(b[i]);
        }
        return state.part;
    }

    function pushZeros(uint256 n, bytes1 last) external returns (bytes1, uint256) {
        bytes1 first;
        for (uint256 i = 0; i < n; i++) {
            first = data.push();
        }
        data.push() = last;
        return (first, data.length);
    }

    function cycle(uint256 up, uint256 down) external returns (bytes memory) {
        for (uint256 i = 0; i < up; i++) {
            data.push(bytes1(uint8(i + 1)));
        }
        for (uint256 i = 0; i < down; i++) {
            data.pop();
        }
        return data;
    }

    function twice(uint256 a) external pure returns (uint256) {
        return Fees.twice(a);
    }
}
