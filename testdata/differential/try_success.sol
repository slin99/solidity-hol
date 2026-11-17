// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

struct SuccessRecord {
    uint256 n;
    string text;
}

interface ISuccessPeer {
    function scalar(bytes calldata data, bool fail) external returns (uint8);
    function pair(bytes calldata data, bool fail) external returns (uint256, bool);
    function dynamicValues(bytes calldata data, bool fail) external returns (string memory, bytes memory);
    function record(bytes calldata data, bool fail) external returns (SuccessRecord memory);
}

contract TrySuccess {
    function scalarNamed(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).scalar(data, fail) returns (uint8 n) { return n; }
        catch { return 999; }
    }
    function scalarOmitted(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).scalar(data, fail) { return 1; }
        catch { return 999; }
    }
    function scalarUnnamed(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).scalar(data, fail) returns (uint8) { return 1; }
        catch { return 999; }
    }
    function pairFirst(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).pair(data, fail) returns (uint256 n, bool) { return n; }
        catch { return 999; }
    }
    function pairSecond(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).pair(data, fail) returns (uint256, bool b) { return b ? 1 : 0; }
        catch { return 999; }
    }
    function pairUnnamed(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).pair(data, fail) returns (uint256, bool) { return 1; }
        catch { return 999; }
    }
    function pairOmitted(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).pair(data, fail) { return 1; }
        catch { return 999; }
    }
    function dynamicNamed(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).dynamicValues(data, fail) returns (string memory s, bytes memory b) {
            return bytes(s).length * 100 + b.length;
        } catch { return 999; }
    }
    function dynamicFirst(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).dynamicValues(data, fail) returns (string memory s, bytes memory) {
            return bytes(s).length;
        } catch { return 999; }
    }
    function dynamicSecond(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).dynamicValues(data, fail) returns (string memory, bytes memory b) {
            return b.length;
        } catch { return 999; }
    }
    function dynamicUnnamed(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).dynamicValues(data, fail) returns (string memory, bytes memory) { return 1; }
        catch { return 999; }
    }
    function dynamicOmitted(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).dynamicValues(data, fail) { return 1; }
        catch { return 999; }
    }
    function structNamed(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).record(data, fail) returns (SuccessRecord memory s) {
            return s.n + bytes(s.text).length;
        } catch { return 999; }
    }
    function structUnnamed(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).record(data, fail) returns (SuccessRecord memory) { return 1; }
        catch { return 999; }
    }
    function structOmitted(address target, bytes calldata data, bool fail) external returns (uint256) {
        try ISuccessPeer(target).record(data, fail) { return 1; }
        catch { return 999; }
    }
}
