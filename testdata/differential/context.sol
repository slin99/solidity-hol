// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Dispatch (payable, nonpayable, receive, fallback) and the call context.
contract Context {
    event Received(address indexed sender, uint256 value);
    event Fallback(uint256 value) anonymous;
    event Noted(uint8 indexed tag, bool flag, bytes32 data);
    event Plain(uint256 value);
    event Typed(int8 indexed a, bytes4 indexed b, bool indexed c);
    event Four(uint256 indexed a, uint256 indexed b, uint256 indexed c, uint256 indexed d) anonymous;

    uint256 private deposits;
    address private last;
    mapping(address => uint256) private balances;
    address private owner;

    receive() external payable {
        deposits += msg.value;
        emit Received(msg.sender, msg.value);
    }

    fallback() external payable {
        emit Fallback(msg.value);
    }

    function deposit() external payable returns (uint256) {
        deposits += msg.value;
        last = msg.sender;
        return deposits;
    }

    function self() external view returns (address) {
        return address(this);
    }

    function sender() external view returns (address) {
        return msg.sender;
    }

    function origin() external view returns (address) {
        return tx.origin;
    }

    function blockInfo() external view returns (uint256, uint256, uint256, address) {
        return (block.number, block.timestamp, block.chainid, block.coinbase);
    }

    function feeInfo() external view returns (uint256, uint256, uint256) {
        return (tx.gasprice, block.basefee, block.gaslimit);
    }

    function typed(int8 a, bytes4 b, bool c) external {
        emit Typed(a, b, c);
    }

    function four() external {
        emit Four(1, 2, 3, 4);
    }

    function emitThenCheck(uint256 x) external {
        emit Plain(x);
        require(x == 0, "nonzero");
    }

    function note(uint8 tag, bool flag, bytes32 data) external {
        emit Noted(tag, flag, data);
    }

    function narrow(uint8 a, int16 b, bytes2 c, bool d) external pure returns (uint8, int16, bytes2, bool) {
        return (a, b, c, d);
    }

    // Helpers that take the call context: one reads nothing else, one reads storage.
    function callerOf() internal view returns (address) {
        return msg.sender;
    }

    function isOwner() internal view returns (bool) {
        return msg.sender == owner;
    }

    function myBalance() external view returns (uint256) {
        return balances[msg.sender];
    }

    function ownerBalance() external view returns (uint256) {
        require(msg.sender == owner, "not owner");
        return balances[msg.sender];
    }

    function caller() external view returns (address) {
        return callerOf();
    }

    function ownerCheck() external view returns (bool) {
        return isOwner();
    }

    function emitIf(bool flag, uint256 x) external {
        if (flag) {
            emit Plain(x);
        }
    }

    // Recursion with storage writes and logs at each level.
    function tally(uint256 n) public returns (uint256) {
        if (n == 0) {
            return 0;
        }
        deposits += n;
        emit Plain(n);
        return n + tally(n - 1);
    }
}
