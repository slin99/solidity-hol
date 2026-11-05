// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IToken {
    function balanceOf(address account) external view returns (uint256);
    function transfer(address to, uint256 value) external returns (bool);
}

// Contract-typed values: state, immutable, local, parameter, return value,
// mapping key and array element, compared and converted, and called through.
contract Holder {
    IToken private token;
    IToken private immutable fixedToken;
    mapping(IToken => uint256) private seen;
    IToken[] private tokens;
    uint256 private calls;

    constructor() {
        fixedToken = IToken(address(0x5000));
    }

    function setToken(IToken t) external {
        token = t;
        tokens.push(t);
    }

    function current() external view returns (IToken) {
        return token;
    }

    function balanceVia(address account) external view returns (uint256) {
        IToken t = token;
        return t.balanceOf(account);
    }

    function fixedBalance(address account) external view returns (uint256) {
        return fixedToken.balanceOf(account);
    }

    function listedBalance(uint256 i, address account) external view returns (uint256) {
        return tokens[i].balanceOf(account);
    }

    function record(IToken t, address account) external returns (uint256) {
        seen[t] = t.balanceOf(account) + 1;
        return seen[t];
    }

    function same(IToken t) external view returns (bool, bool) {
        return (t == token, address(t) == address(fixedToken));
    }

    function pay(address to, uint256 value) external returns (bool) {
        return token.transfer(to, value);
    }

    function bump(uint256 by) external returns (uint256) {
        calls += by;
        return calls;
    }

    // The call through this runs the deployed code, whose write is seen after.
    function selfCall(uint256 by) external returns (uint256) {
        return this.bump(by) + calls;
    }
}
