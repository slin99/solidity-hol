// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.37;

interface IExpressionPeer {
    function ping(uint256 value) external;
}

contract ExpressionMembers {
    enum Choice { First, Second }
    uint8 a;
    uint8 b;
    bool flag;
    bytes4 tag;
    address who;
    Choice choice;
    int16 signedValue;
    uint256 public count;
    mapping(uint256 => uint256) entries;
    uint8[3] values;
    struct Pair { uint8 first; uint8 second; }
    Pair pair;
    IExpressionPeer constant BAD = IExpressionPeer(address(uint160(1) / uint160(0)));

    function clearPacked() external returns (uint8, uint8, bool, bytes4, address, Choice, int16) {
        a = 7; b = 8; flag = true; tag = 0x12345678;
        who = address(0x1234); choice = Choice.Second; signedValue = -5;
        delete b; delete flag; delete tag; delete who; delete choice; delete signedValue;
        return (a, b, flag, tag, who, choice, signedValue);
    }

    function index(uint256 i) internal returns (uint256) { count++; return i; }

    function clearIndex(uint256 i) external returns (uint256, uint8, uint8, uint8) {
        delete values[index(i)];
        return (count, values[0], values[1], values[2]);
    }

    function clearMapping(uint256 key) external returns (uint256, uint256) {
        entries[key] = 99;
        delete entries[index(key)];
        return (entries[key], count);
    }

    function clearField() external returns (uint8, uint8) {
        delete pair.first;
        return (pair.first, pair.second);
    }

    function clearLocal() external pure returns (uint8) {
        uint8 x = 9;
        delete x;
        return x;
    }

    function balanceOf(address target) external view returns (uint256) { return target.balance; }
    function ownBalance() external payable returns (uint256, uint256) {
        return (address(this).balance, payable(address(this)).balance);
    }
    function receiver(address target) internal returns (address) { count++; return target; }
    function computedBalance(address target) external payable returns (uint256, uint256) {
        uint256 result = receiver(target).balance;
        return (result, count);
    }

    function peer(address target) internal returns (IExpressionPeer) {
        count++;
        return IExpressionPeer(target);
    }
    function computedSelector(address target) external returns (bytes4, uint256) {
        bytes4 result = peer(target).ping.selector;
        return (result, count);
    }
    function variableSelector(IExpressionPeer target) external pure returns (bytes4) {
        return target.ping.selector;
    }
    function selectorAssignment(IExpressionPeer target) external pure returns (address, bytes4) {
        return (address(target), (target = IExpressionPeer(address(0))).ping.selector);
    }
    function getterSelector(ExpressionMembers target) external view returns (bytes4) {
        return target.count.selector;
    }
    function failingSelector() external pure returns (bytes4) { return BAD.ping.selector; }
    function boundsSelector(uint256 i) external view returns (bytes4) {
        return IExpressionPeer(address(uint160(values[i]))).ping.selector;
    }

    function fixedLength(bytes1 x, bytes8 y, bytes32 z) external pure returns (uint8, uint8, uint8) {
        return (x.length, y.length, z.length);
    }
    function bytesReceiver() internal returns (bytes8) { count++; return bytes8(0); }
    function computedLength() external returns (uint8, uint256) {
        uint8 result = bytesReceiver().length;
        return (result, count);
    }
    function checkedLength(uint256 i) external pure returns (uint8) {
        return bytes8(uint64(1 / i)).length;
    }
    function lengthAssignment(bytes8 x) external pure returns (bytes8, uint8) {
        return (x, (x = bytes8(0)).length);
    }
}
