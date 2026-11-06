// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IReceiver {
    function onReceived(address from, uint256 amount, bytes calldata data) external returns (bytes4);
}

error Denied(address who);

library Registry {
    event Registered(uint256 id);

    function register(uint256 id) public returns (uint256) {
        emit Registered(id);
        return id;
    }
}

contract Hashes {
    bytes32 public constant ROLE = keccak256("MINTER_ROLE");

    event Moved(address indexed from, uint256 amount);

    bytes public blob;
    mapping(bytes32 => uint256) public seen;
    uint256 public calls;

    function ofBytes(bytes memory b) public pure returns (bytes32) {
        return keccak256(b);
    }

    function ofCalldata(bytes calldata b) external pure returns (bytes32) {
        return keccak256(b);
    }

    function ofLiterals() public pure returns (bytes32, bytes32, bytes32) {
        return (keccak256(""), keccak256(hex"1901"), keccak256("Permit(address owner)"));
    }

    function ofStorage() public view returns (bytes32) {
        return keccak256(blob);
    }

    function setBlob(bytes memory b) public {
        blob = b;
    }

    function record(bytes memory b) public returns (uint256) {
        bytes32 h = keccak256(b);
        seen[h] += 1;
        return seen[h];
    }

    function next() internal returns (bytes memory) {
        calls += 1;
        if (calls == 1) return "one";
        return "more";
    }

    function ofCall() public returns (bytes32) {
        return keccak256(next());
    }

    function isRole(bytes32 r) public pure returns (bool) {
        return r == ROLE;
    }

    function selectors() public pure returns (bytes4, bytes4, bytes4) {
        return (IReceiver.onReceived.selector, this.ofBytes.selector, Denied.selector);
    }

    function eventSelector() public pure returns (bytes32) {
        return Moved.selector;
    }

    function librarySelectors() public pure returns (bytes4, bytes32) {
        return (Registry.register.selector, Registry.Registered.selector);
    }

    function widened() public pure returns (bytes32, uint32) {
        bytes32 w = IReceiver.onReceived.selector;
        return (w, uint32(this.ofBytes.selector));
    }

    function checkReply(bytes4 reply) public pure returns (bool) {
        return reply == IReceiver.onReceived.selector;
    }
}
