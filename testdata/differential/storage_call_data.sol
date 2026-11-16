// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Storage bytes passed as low-level call data, read where they are. Each
// function clears what it stored, so only the peer's writes remain.
contract StorageCallData {
    struct Motion {
        bytes[] data;
    }

    // The peer's delegatecall code writes slot 0.
    uint256 private counter;
    bytes private payload;
    Motion private motion;

    function callStored(address target, bytes memory data) public returns (bool ok, bytes memory r) {
        payload = data;
        (ok, r) = target.call(payload);
        delete payload;
    }

    function staticStored(address target, bytes memory data) public returns (bool ok, bytes memory r) {
        payload = data;
        (ok, r) = target.staticcall(payload);
        delete payload;
    }

    function delegateStored(address target, bytes memory data)
        public returns (bool ok, bytes memory r, uint256)
    {
        payload = data;
        (ok, r) = target.delegatecall(payload);
        delete payload;
        return (ok, r, counter);
    }

    function callElement(address target, bytes memory data) public returns (bool ok, bytes memory r) {
        motion.data.push(data);
        (ok, r) = target.call(motion.data[motion.data.length - 1]);
        motion.data.pop();
    }

    // Returns its whole argument, so a call to it observes every byte sent.
    function echo(bytes calldata d) external pure returns (bytes memory) {
        return d;
    }
}
