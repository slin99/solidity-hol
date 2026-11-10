// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;
import "./udvt_types.sol";

library Named {
    type Code is bytes4;
    function code() internal pure returns (Code) { return Code.wrap(0x12345678); }
}
contract NominalBase {
    function pick(Amount) internal virtual returns (uint256) { return 1; }
    function pick(OtherAmount) internal virtual returns (uint256) { return 2; }
    function pick(uint16) internal virtual returns (uint256) { return 3; }
    function pick(address) internal virtual returns (uint256) { return 4; }
    function pick(NominalBase) internal virtual returns (uint256) { return 5; }
}
contract UDVT is NominalBase {
    type Local is uint8;
    Amount public stored;
    uint16 public neighbour;
    mapping(Amount => Amount) values;
    Amount[2] fixedValues;
    Amount[] history;
    struct Entry { Amount amount; Local local; }
    Entry entry;
    uint256 counter;
    Amount public immutable seed;
    Amount public constant LIMIT = Amount.wrap(42);
    event Changed(Amount indexed key, Amount value);
    error TooLarge(Amount value);

    constructor(Amount a) { seed = a; stored = a; }
    function dirtyWrap(uint256 x) external pure returns (uint16) {
        uint16 narrow;
        assembly { narrow := x }
        return Amount.unwrap(Amount.wrap(narrow));
    }
    function identity(Amount a) external pure returns (Amount) { return Amount.wrap(Amount.unwrap(a)); }
    function kinds(Signed s, Flag b, Tag t, Account a) external pure returns (int8, bool, bytes4, address) {
        return (Signed.unwrap(Signed.wrap(Signed.unwrap(s))),
                Flag.unwrap(Flag.wrap(Flag.unwrap(b))),
                Tag.unwrap(Tag.wrap(Tag.unwrap(t))),
                Account.unwrap(Account.wrap(Account.unwrap(a))));
    }
    function qualified() external pure returns (bytes4, uint8) {
        return (Named.Code.unwrap(Named.code()), Local.unwrap(Local.wrap(7)));
    }
    function save(Amount key, Amount value) external returns (Amount, Amount, Amount, Amount) {
        stored = value;
        neighbour = 9;
        values[key] = value;
        fixedValues[1] = value;
        history.push(value);
        entry.amount = value;
        entry.local = Local.wrap(7);
        return (values[key], fixedValues[1], history[0], entry.amount);
    }
    function announce(Amount key, Amount value) external { emit Changed(key, value); }
    function fail(Amount value) external pure { revert TooLarge(value); }
    function roundtrip(Amount a) external pure returns (Amount) {
        return abi.decode(abi.encode(a), (Amount));
    }
    function viaThis(Amount a) external view returns (Amount) { return this.identity(a); }
    function calldataArray(Amount[] calldata a) external pure returns (Amount) { return a[1]; }
    function memoryArray() external pure returns (Amount) {
        Amount[] memory a = new Amount[](2);
        a[1] = Amount.wrap(17);
        return a[1];
    }
    function operators(Amount a, Amount b) external pure returns (Amount, Amount, Amount, Amount, bool, Amount) {
        return (a + b, a - b, -a, ~a, a == b, a.twice());
    }
    function checkedInUnchecked(Amount a, Amount b) external pure returns (Amount) {
        unchecked { return a + b; }
    }
    function bump() internal returns (Amount) { counter++; return Amount.wrap(uint16(counter)); }
    function order() external returns (Amount, uint256) { Amount a = bump() - bump(); return (a, counter); }
    function wrappedEffect() external returns (uint16, uint256) { return (Amount.unwrap(bump()), counter); }
    function rollback() external returns (Amount) { counter = 99; return Amount.wrap(65535) + Amount.wrap(1); }
    function nominal() external returns (uint256, uint256, uint256, uint256, uint256) {
        return (super.pick(Amount.wrap(0)), super.pick(OtherAmount.wrap(0)), super.pick(uint16(0)),
                super.pick(address(0)), super.pick(NominalBase(address(0))));
    }
}
