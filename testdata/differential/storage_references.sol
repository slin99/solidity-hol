// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

struct Checkpoint {
    uint48 key;
    uint208 value;
}

struct History {
    Checkpoint[] checkpoints;
}

library Trace {
    function unsafeAt(Checkpoint[] storage self, uint256 pos) internal view returns (Checkpoint storage) {
        return self[pos];
    }

    function length(History storage self) internal view returns (uint256) {
        return self.checkpoints.length;
    }

    function latest(History storage self) internal view returns (uint208) {
        uint256 pos = self.checkpoints.length;
        return pos == 0 ? 0 : unsafeAt(self.checkpoints, pos - 1).value;
    }

    function append(History storage self, uint48 key, uint208 value) internal returns (uint256) {
        Checkpoint storage last = self.checkpoints.push();
        last.key = key;
        last.value = value;
        return self.checkpoints.length;
    }

    function setLatest(History storage self, uint48 key, uint208 value) internal returns (uint208 old) {
        Checkpoint[] storage ckpts = self.checkpoints;
        uint256 pos = ckpts.length;
        require(pos > 0, "empty");
        Checkpoint storage last = unsafeAt(ckpts, pos - 1);
        require(last.key <= key, "decreasing key");
        old = last.value;
        last.key = key;
        last.value = value;
    }
}

contract StorageReferences {
    using Trace for History;

    enum Color {
        Red,
        Green,
        Blue
    }

    struct Slot {
        uint256 value;
    }

    struct Pair {
        uint128 a;
        uint128 b;
        mapping(uint256 => uint256) extra;
    }

    History history;
    mapping(bytes32 => Slot) slots;
    mapping(uint256 => Pair) pairs;
    mapping(uint256 => mapping(uint256 => uint256)) grid;
    Pair[] list;
    Color[] colors;

    function appendCheckpoint(uint48 key, uint208 value) public returns (uint256, uint208) {
        uint256 n = history.append(key, value);
        return (n, history.latest());
    }

    function record(uint48 key, uint208 value) public returns (uint208, uint208, uint256) {
        uint208 old = history.setLatest(key, value);
        return (old, history.latest(), history.length());
    }

    function slotOf(bytes32 k) internal view returns (Slot storage) {
        return slots[k];
    }

    function slotNamed(bytes32 k) internal view returns (Slot storage r) {
        r = slots[k];
    }

    function viaSlot(bytes32 k, uint256 v) public returns (uint256, uint256) {
        slotOf(k).value = v;
        slotNamed(k).value += 1;
        return (slots[k].value, slotOf(k).value);
    }

    function pairOf(uint256 k) internal view returns (Pair storage p) {
        p = pairs[k];
    }

    function viaPair(uint256 k, uint128 a) public returns (uint128, uint256, uint256) {
        Pair storage p = pairOf(k);
        p.a = a;
        pairOf(k).b = a + 1;
        pairOf(k).extra[a] = 7;
        p.extra[a] += 1;
        return (pairs[k].b, pairs[k].extra[a], uint256(pairOf(k).a));
    }

    function row(uint256 i) internal view returns (mapping(uint256 => uint256) storage) {
        return grid[i];
    }

    function viaRow(uint256 i, uint256 j, uint256 v) public returns (uint256, uint256) {
        mapping(uint256 => uint256) storage r = row(i);
        r[j] = v;
        row(i)[j + 1] = v + 1;
        return (grid[i][j], row(i)[j + 1]);
    }

    function lastOf(Pair[] storage xs) internal view returns (Pair storage) {
        return xs[xs.length - 1];
    }

    function viaList(uint128 a) public returns (uint256, uint128, uint128) {
        Pair storage last = lastOf(list);
        last.a = a;
        lastOf(list).b = a - 1;
        return (list.length, list[list.length - 1].a, list[list.length - 1].b);
    }

    function pushPair(uint128 a) public returns (uint256, uint128, uint128) {
        Pair storage p = list.push();
        p.a = a;
        p.extra[a] = 1;
        return (list.length, list[list.length - 1].a, list[list.length - 1].b);
    }

    function addColor(Color c) public returns (uint256, Color, Color) {
        colors.push(c);
        Color[] storage cs = colors;
        return (cs.length, cs[cs.length - 1], colors[0]);
    }
}
