// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.37;

contract EnumKeysGetters {
    enum Module { Operators, Clusters, Views, Dao }

    Module internal constant DEFAULT_MODULE = Module.Clusters;
    Module public constant LAST_MODULE = Module.Dao;

    struct Inner {
        uint64 amount;
        Module module;
        bytes data;
        uint16[] list;
    }

    struct Outer {
        uint256 id;
        Inner inner;
        mapping(uint256 => uint256) skippedMapping;
        uint8[] skippedArray;
        address owner;
    }

    mapping(Module => address) public modules;
    mapping(Module => mapping(Module => uint16)) public pairs;
    mapping(Module => Outer) public outers;
    Outer public single;

    function setModule(Module m, address a) external returns (address) {
        modules[m] = a;
        return modules[m];
    }

    function readModule(Module m) external view returns (address) {
        return modules[m];
    }

    function setDefault(address a) external returns (address, address) {
        modules[DEFAULT_MODULE] = a;
        return (modules[Module.Clusters], modules[LAST_MODULE]);
    }

    function setPair(Module a, Module b, uint16 v) external returns (uint16) {
        pairs[a][b] = v;
        return pairs[a][b];
    }

    function defaultModule() external pure returns (Module) {
        return DEFAULT_MODULE;
    }

    function isLast(Module m) external pure returns (bool, uint8) {
        return (m == LAST_MODULE, uint8(LAST_MODULE));
    }

    function setOuter(Module k, uint256 id, uint64 amount, Module m, bytes calldata data,
                      uint16 first, address owner) external {
        Outer storage o = outers[k];
        o.id = id;
        o.inner.amount = amount;
        o.inner.module = m;
        o.inner.data = data;
        o.inner.list.push(first);
        o.inner.list.push(first + 1);
        o.skippedArray.push(9);
        o.skippedMapping[id] = 7;
        o.owner = owner;
    }

    function setSingle(uint256 id, uint64 amount, bytes calldata data) external {
        single.id = id;
        single.inner.amount = amount;
        single.inner.module = DEFAULT_MODULE;
        single.inner.data = data;
        single.owner = msg.sender;
    }
}
