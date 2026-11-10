// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

type Amount is uint16;
type OtherAmount is uint16;
type Signed is int8;
type Flag is bool;
type Tag is bytes4;
type Account is address;
uint16 constant EXTRA = 1;

using {add as +, subtract as -, negate as -, invert as ~, equal as ==, twice} for Amount global;

function add(Amount a, Amount b) pure returns (Amount) {
    return Amount.wrap(Amount.unwrap(a) + Amount.unwrap(b) + EXTRA);
}
function subtract(Amount a, Amount b) pure returns (Amount) {
    return Amount.wrap(Amount.unwrap(a) * 10 - Amount.unwrap(b));
}
function negate(Amount a) pure returns (Amount) {
    return Amount.wrap(100 - Amount.unwrap(a));
}
function invert(Amount a) pure returns (Amount) {
    return Amount.wrap(~Amount.unwrap(a));
}
function equal(Amount a, Amount b) pure returns (bool) {
    return Amount.unwrap(a) % 10 == Amount.unwrap(b) % 10;
}
function twice(Amount a) pure returns (Amount) {
    return helper(a);
}
function helper(Amount a) pure returns (Amount) {
    return Amount.wrap(2 * Amount.unwrap(a));
}
