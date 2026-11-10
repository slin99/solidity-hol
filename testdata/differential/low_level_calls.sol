// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface Peer {
    function value(uint256 x) external pure returns (uint256);
    function context() external payable returns (address, uint256, address, uint256);
    function balanceOf(address a) external view returns (uint256);
    function read() external view returns (uint256);
}

contract LowLevelCalls {
    uint256 private counter;
    uint256 private trace;

    function raw(address target, bytes memory data) public view returns (bool, bytes memory) {
        return target.staticcall(data);
    }

    function rawPayable(address payable target, bytes memory data) public view returns (bool, bytes memory) {
        return target.staticcall(data);
    }

    function doubled(address target, bytes memory data) public view returns (bool, uint256) {
        (bool ok, bytes memory result) = target.staticcall(data);
        uint256 r;
        if (ok) r = abi.decode(result, (uint256));
        return (ok, r);
    }

    function twice(address target, bytes memory first, bytes memory second)
        public view returns (bytes memory, bytes memory, bytes memory)
    {
        (, bytes memory a) = target.staticcall(first);
        (, bytes memory b) = target.staticcall(second);
        return (a, b, first);
    }

    function rawCall(address target, uint256 amount, bytes memory data)
        public payable returns (bool, bytes memory)
    {
        return target.call{value: amount}(data);
    }

    // Whether the call succeeded, then this contract's and the target's
    // balances after it.
    function callBalances(address payable target, uint256 amount, bytes memory data)
        public payable returns (bool, uint256, uint256)
    {
        (bool ok, ) = target.call{value: amount}(data);
        return (ok, Peer(target).balanceOf(address(this)), Peer(target).balanceOf(target));
    }

    // Whether the call succeeded, then the target's counter after it.
    function callAndRead(address target, bytes memory data) public returns (bool, uint256) {
        (bool ok, ) = target.call(data);
        return (ok, Peer(target).read());
    }

    function rawCallGas(address target, uint256 limit, bytes memory data)
        public returns (bool, bytes memory)
    {
        return target.call{gas: limit}(data);
    }

    // A literal is passed where it is, so the call allocates nothing.
    function plainTransfer(address payable target, uint256 amount)
        public payable returns (bool, bytes memory, bytes memory)
    {
        (bool ok, bytes memory r) = target.call{value: amount}("");
        return (ok, r, new bytes(1));
    }

    function rawDelegate(address target, bytes memory data)
        public payable returns (bool, bytes memory, uint256)
    {
        (bool ok, bytes memory r) = target.delegatecall(data);
        return (ok, r, counter);
    }

    function rawDelegateGas(address target, uint256 limit, bytes memory data)
        public returns (bool, uint256)
    {
        (bool ok, ) = target.delegatecall{gas: limit}(data);
        return (ok, counter);
    }

    // Calldata bytes are passed where they are: only the result moves the
    // free memory pointer.
    function staticCalldata(address target, bytes calldata data)
        public view returns (bool, bytes memory, uint256)
    {
        (bool ok, bytes memory r) = target.staticcall(data);
        uint256 free;
        assembly { free := mload(0x40) }
        return (ok, r, free);
    }

    function callCalldata(address target, uint256 amount, bytes calldata data)
        public payable returns (bool, bytes memory)
    {
        return target.call{value: amount}(data);
    }

    function delegateCalldata(address target, bytes calldata data)
        public returns (bool, bytes memory, uint256)
    {
        (bool ok, bytes memory r) = target.delegatecall(data);
        return (ok, r, counter);
    }

    // Each element of a calldata array is delegate-called in turn.
    function multicall(address target, bytes[] calldata calls) public returns (uint256) {
        for (uint256 i = 0; i < calls.length; i++) {
            (bool ok, ) = target.delegatecall(calls[i]);
            require(ok);
        }
        return counter;
    }

    // The callee calls bump back before the call returns.
    function reentered(address target) public returns (bool, uint256) {
        counter = 10;
        (bool ok, ) = target.call(abi.encodeWithSignature("reenter()"));
        return (ok, counter);
    }

    function bump() public { counter += 1; }

    function highGas(Peer peer, uint256 limit) public view returns (uint256) {
        return peer.value{gas: limit}(21);
    }

    function highValueGas(Peer peer, uint256 amount, uint256 limit)
        public payable returns (address, uint256, address, uint256)
    {
        return peer.context{value: amount, gas: limit}();
    }

    // Operands are evaluated target first, then the options as written,
    // then the data.
    function order(address payable target) public payable returns (uint256, uint256) {
        trace = 0;
        (bool ok, ) = target.call{gas: mark(1, 100000), value: mark(2, 1)}(tail(3));
        require(ok);
        uint256 first = trace;
        trace = 0;
        (bool ok2, ) = target.call{value: mark(1, 1), gas: mark(2, 100000)}(tail(3));
        require(ok2);
        return (first, trace);
    }

    function mark(uint256 k, uint256 v) internal returns (uint256) {
        trace = trace * 10 + k;
        return v;
    }

    function tail(uint256 k) internal returns (bytes memory) {
        trace = trace * 10 + k;
        return "";
    }
}
