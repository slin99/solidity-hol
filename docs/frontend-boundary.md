# Initial compiler frontend boundary

This document records observations from the initial Solidity 0.8.37 via-IR
reconnaissance corpus. It is evidence for the imported and elaborated HOL
representations, not a claim of complete AST coverage.

The reproducible artifact is
[`testdata/frontend/expected/reconnaissance.json`](../testdata/frontend/expected/reconnaissance.json).
It is generated with:

```sh
tools/export_solc_artifacts.py \
  --solc /path/to/solc-0.8.37 \
  --output testdata/frontend/expected/reconnaissance.json \
  testdata/frontend/types.sol \
  testdata/frontend/evaluation_order.sol \
  testdata/frontend/storage_references.sol
```

The pure-subset importer fixture
[`testdata/frontend/expected/pure_core.json`](../testdata/frontend/expected/pure_core.json)
is generated the same way from `testdata/frontend/pure_core.sol`.

Core artifacts retain the analyzed AST, ABI, storage layouts, initcode, deployed
bytecode, immutable references and method identifiers. They omit textual `ir`
and `irOptimized`, which the core importer does not read. Checked preparation
requires this output selection; regenerate older artifacts with the exporter.
For the compiler's Yul, use `tools/export_solc_yul.py` (ASTs) or
`tools/yul_reconnaissance.py` (textual IR analysis); those tools request their
own outputs.

## Boundary layers

The implementation should distinguish three representations:

1. raw Standard JSON and the compiler-produced analyzed AST;
2. a validated, normalized AST retaining source and declaration identity; and
3. a smaller executable core with explicit effect schedules and operations.

Artifact consumers enter through `solidityPrepareLib`: check the pinned
compiler/profile/settings contract, import, validate the source, elaborate,
and check the full core with cv evaluation. Raw import and elaboration remain
available with these checks as caller preconditions. Unknown forms and missing
required annotations have distinct unsupported and malformed diagnostics.

The general `wf_core_program env prog` predicate retains its environment-relative
contract: it checks the declarations supplied by `env`. Checked preparation and
execution instantiate it with `core_program_environment prog`, whose declarations
come directly from the program. This keeps existing lookup/entry consequences
available without strengthening their premises.

## Identity and source positions

Every observed AST node has a numeric `id`, a `nodeType`, and a compact `src`
range. Declarations are referenced through numeric `referencedDeclaration`
fields. Source-unit `exportedSymbols`, variable `scope`, function `scope`, and
`linearizedBaseContracts` also contain declaration IDs. Names are therefore
diagnostic data, not semantic identity.

A normalized program will need distinct HOL wrappers or disciplined uses for at
least source IDs, node IDs, declaration IDs, and contract IDs. Import must check
that referenced IDs exist and have the expected declaration kind.

## Types and locations

Expressions and declarations carry `typeDescriptions` with both a display
`typeString` and an encoded `typeIdentifier`. Type-name subtrees provide
structural information through nodes such as `ElementaryTypeName`,
`ArrayTypeName`, `Mapping`, and `UserDefinedTypeName`.

The corpus confirms that semantic distinctions occur across several fields:

- declarations have `storageLocation`;
- type identifiers distinguish storage references, storage pointers, memory
  pointers, and calldata pointers;
- the display string is context-dependent and sometimes omits a location that
  appears in the identifier;
- user-defined types refer to their declarations by ID; and
- literal types include rational compile-time constants rather than only runtime
  integer types.

The importer must not treat `typeString` as a canonical type grammar. It should
construct normalized types from structural nodes, declaration links, location
annotations, and validated type identifiers. Encoded identifiers remain useful
for consistency checks and for distinctions not represented structurally at a
particular node.

The initial corpus includes integers, addresses, fixed bytes, dynamic arrays,
mappings, structs, enums, a user-defined value type, tuples, and internal and
event function types. It does not establish complete coverage of function
pointer types, fixed arrays, strings, dynamic bytes, payable addresses, contract
types, or every literal category.

## Expressions and calls

Numeric literals retain solc's exact rational type annotation, including the
scale of `wei`, `gwei`, `ether`, `seconds`, `minutes`, `hours`, `days` and
`weeks`. Elaboration uses that annotation for decimal, hexadecimal and
scientific notation and folded integer expressions; it does not round through
floating point or multiply a unit literal a second time. Fractional literals
are admitted as operands of supported expressions folded to integers.
Address literals have the distinct `t_address` annotation. The importer
validates their 40 hexadecimal digits and normalizes their value to decimal;
elaboration checks the 160-bit bound and produces an address value.

Observed expression nodes include identifiers, literals, member and index
access, tuple expressions, assignments, binary operations, and function calls.
The AST already supplies useful analyzed annotations:

- identifiers and most member accesses have `referencedDeclaration`;
- calls distinguish `functionCall`, `structConstructorCall`, and
  `typeConversion` through `kind`;
- binary operations provide `commonType`;
- expression nodes record `isConstant`, `isLValue`, `isPure`, and
  `lValueRequested`; and
- calls record positional arguments, optional argument names, and `tryCall`.

Not every builtin member operation has a declaration ID. In the corpus,
array `push` and `pop` are member accesses with no `referencedDeclaration` and
must be recognized from the receiver type and member name. Type conversions use
an `ElementaryTypeNameExpression` rather than a declaration reference.

The AST does not contain a general, normative evaluation-order annotation.
Argument arrays preserve source positions, but that alone is not a compiler
schedule. Profile elaboration must assign construct-specific schedules. The
emitted IR is useful evidence for Solidity 0.8.37 via IR, but compiler-generated
IR is not initially a stable frontend interface.

## Statements and declarations

The corpus currently observes blocks, expression statements, variable
declaration statements, returns, and event emission. A variable declaration
statement separately records declaration nodes and an `assignments` list of IDs;
this is important for tuple declarations and holes even though the current
corpus contains only single declarations.

Function definitions already record visibility, mutability, kind, virtuality,
parameters, return parameters, modifiers, implementation status, and optional
selectors. Contract definitions record inheritance-related and used-event/error
metadata. Inheritance needs two of these annotations (the differential fixture
`inheritance.sol`): the importer flattens a contract along its
`linearizedBaseContracts`, and `call_table` resolves overrides through each
function's `baseFunctions`. A public state variable, constant or immutable may
override an external function. The importer removes the transitively replaced
functions using the variable's `baseFunctions`, leaving its getter as the sole
dispatch entry for that selector. Base-constructor specifiers on constructors
(`constructors.sol`) use their `referencedDeclaration`. Unqualified modifier
invocations resolve through the transitive `baseModifiers` relation in the
contract's linearization; explicitly qualified `Base.modifier` invocations
keep their declared target (`virtual_modifiers.sol`). Only invoked modifier
implementations are imported, so overridden bodyless declarations do not
reject a concrete contract. A bodyless modifier still reached by an invocation
makes that function unsupported. A `super.f(...)` call
(`super_calls.sol`) runs what the compiler's lookup finds in the deployed
contract's linearization: the first function after the caller's contract with
the name and parameter types of the declaration the call's
`referencedDeclaration` names. That declaration is resolved from the caller's
own contract, so in a diamond it can differ from the function that runs. The
overridden functions super calls reach are checked and elaborated, but not
dispatched. `super` in a modifier body, an initializer or a base-constructor
argument is rejected.

An explicit `Base.f(...)` call (`qualified_base_calls.sol`) runs the named
declaration's implementation, including its modifiers, even when a derived
function overrides it. Its arguments keep their written evaluation order and
are reordered to the declaration's parameters only afterward. Ordinary calls
inside that implementation still resolve virtually. Static calls in modifier
bodies and initialization expressions also retain the base procedures they
reach. Calls through bodyless declarations use the same transitive
`baseFunctions` table as other virtual calls; an unsupported most-derived
override remains unsupported rather than falling back to a base body.

Event emission resolves a declaration ID for unqualified names, library and
interface names, and names qualified through an imported module
(`qualified_events.sol`). Referenced events from outside the contract's bases,
including file-level declarations, accompany the imported contract. Qualifiers
are declaration names with no runtime evaluation; event arguments retain their
written order, including named arguments. Log encoding and transaction rollback
use the ordinary event semantics.

Inline assembly writes a scalar local back only if decoding its word and
encoding the resulting value reproduces that exact word. Non-canonical
`uintN`, `intN`, `bool`, address and `bytesN` words fail closed with
`InvalidCompletion`; they are not silently cleaned. Canonical negative signed
words are sign-extended and fixed-byte words are left-aligned.

Inline assembly reads a storage pointer local's `x.slot` and `x.offset` as
its reference's slot and offset (`assembly_pointers.sol`). Assigning `x.slot`,
as OpenZeppelin's `StorageSlot` and ERC-7201 namespaced storage getters do,
points the local at that slot of the executing account, at offset 0, with its
declared type; the compiler rejects assigning `x.offset`.

Inline assembly reads a memory `bytes` or `string` local as its address
(`assembly_memory.sol`). The source heap gives each object the address the
compiler's allocator would (`object_address`: `0x80` plus the memory
allocated so far, `0x60` for the shared empty object), and a block runs over
a memory holding each byte sequence's length word and bytes there. Under
`memoryguard` the compiler may start its free memory pointer above `0x80`, so
arithmetic relative to a pointer is modelled but returning, storing or
comparing a raw pointer value is outside the boundary. The block's memory also
holds the free memory pointer at `0x40`, `0x80` plus the memory allocated so
far, under the same boundary; a block that exits normally may not change it,
and what it wrote from it up is dropped (the temporary memory the Solidity
docs allow a memory-safe block). A literal address with a literal length is
read only at the free memory pointer or where the block wrote it before (an
`mstore`, a call's output region or a `returndatacopy`, also in an argument to
the right, since arguments run right to left), as the elaborator checks. At a computed address a block may read only the free memory pointer,
the zero slot `[0x60, 0x80)`, each byte sequence's length word and data
(zero-padded to whole words where solc's memory holds the zeros: not for
bytes copied from return data, a low-level call's or a `catch`'s, whose
padding solc leaves as it was), and bytes it has written itself; any other read,
another kind of memory object, the scratch space before the block writes it,
or past an object's last word, ends the block with an `InvalidCompletion`.
A callee that returns fewer bytes than the block's output region leaves the
rest unwritten, so reading it fails closed where the EVM reads stale scratch:
OpenZeppelin's `SafeERC20` against a token whose `transfer` returns nothing
runs to that.

Inline assembly's `call`, `staticcall` and `delegatecall` (`assembly_calls.sol`,
`assembly_delegate.sol`) run the callee on Verifereum through `externalCall`,
as high-level and low-level calls do; `delegatecall` runs the callee's code
in this contract's account, with its caller and value. The source
tracks no gas, so `gas()` is admitted only as a call's gas argument, where it
means the fixed budget every call from the source gets, and a literal gas
argument is capped at that budget. The source state keeps the frame's return
data buffer: every high-level, try and low-level call sets it to the callee's
return or revert bytes, and a block starts with it and leaves its own final
buffer behind. `ecrecover` calls a precompile whose return data the source
doesn't compute, so after one the buffer is unknown: a block that could read
it before a call of its own (`returndatasize` or `returndatacopy` not after a
statement of the block that calls, earlier in the same or an enclosing
statement list, or in an argument left of a call, since arguments run right
to left) then fails with an `InvalidCompletion`, and a block that leaves an
empty buffer keeps it unknown. A Yul function's body may read return data only
after a call of its own. A block in a static frame that names `call` or
`delegatecall` fails closed; `staticcall` runs. A block that leaves an
object's padding (the bytes past its length, in its last word) unwritten or
not zero leaves it out of later blocks' memory, where reading it fails closed.
solc lets a block assign a memory
reference (`b := ...`); the elaborator rejects it, since the block reads the
name as a literal.

## Storage layout

`storageLayout` and `transientStorageLayout` are separate from the AST. They contain state-variable entries
with declaration IDs, slots, byte offsets, contract names, and references into a
layout type table. Type-table entries describe encodings such as `inplace`,
`mapping`, and `dynamic_array`, byte widths, member offsets, keys, values, and
base element types.

Source types and layout descriptors must remain separate formal structures. The
compiler initially supplies layout calculation; Solidity-HOL interprets the
layout when reading, writing, and capturing references. The declaration IDs in
layout entries must resolve to compatible state-variable declarations. The importer
interleaves the two tables in declaration order and checks each entry's backend
against its declaration. Transient variables support value types, as solc 0.8.37
does; transient mappings and other reference types are rejected.

Persistent and transient slots have independent numbering. `layout at <expr>`
needs no source expression evaluator here: the compiler resolves the expression
and records absolute persistent slots, including inherited variables and mapping
roots. It leaves transient slots unchanged. These layout calculations are part
of the existing compiler metadata boundary.

Transient scalar reads and writes use `source_world.transient`, retaining the
same packing and cleanup as persistent scalars. A static frame cannot write
either backend. `call_contract` executes a frame, so it retains transient state
across calls and restores it on revert. The transaction driver starts each
transaction with empty transient storage and discards it afterward; it must not
clear it between calls in the same transaction.

Storage declarations now include elementary scalars, structs, scalar-key and byte-sequence-key
mappings, and fixed/dynamic arrays, including their storage combinations.
Scalar leaves can be read and updated through member/index paths.
The importer takes each
contract's `storageLayout.storage` entries in declaration order, with their
slot, byte offset and type identifier; `valid_src_unit` requires one entry per
state variable, naming its declaration and type, and leaves the layout
calculation itself, including that packed variables don't overlap, to the
compiler. Elaboration copies slot and offset into the core program's
`state_variables`. Initialisers are imported and run by the creation
procedure, and so are immutables' (below). Mapping key/value types come from recursive type-name
normalization. AST and layout type identifiers use different encodings; both
are checked against the normalized type. Bytes/string mapping keys retain their
memory, calldata or storage reference, or their literal bytes. Hashing reads
them in place without allocating a memory object or advancing the free-memory
pointer, as the compiler uses scratch memory. Their unpadded contents followed by the root slot's
32-byte big-endian encoding determine the Keccak-256 slot; no length word or
ABI padding is included. Public getters accept the same keys. The scalar leaf width determines
its storage read/write, and aggregate root slots come from the layout. Fixed
array dimensions come from the compiler's resolved integer type of the length
expression. Scalar elements pack without straddling slots; each nested row
starts on a fresh slot. Array indexing checks bounds with panic `0x32`, and
`.length` still evaluates its indexed prefix. Dynamic-array length is read from
its root slot and packed elements start at Keccak-256 of that slot. `push(value)`,
`push()` (also as a scalar lvalue), and `pop()` use the captured location. Empty
pop panics with `0x31`; both push forms follow the pinned compiler's resource
panic `0x41` at length >= `2^64`. Length reads and indexing retain the full
256-bit range. `pop()` clears only the removed scalar bytes; `push()` preserves
existing bytes at the appended position, as the pinned compiler does. Dynamic
array mutation of aggregates, local reference bindings and aggregate copies
remain coverage work.

A public state variable's getter takes one key per mapping and one index per
array along its type, an index past an array's length reverting with no data.
It returns the value it reaches, a byte sequence copied to memory; for a
struct, its members in declaration order, skipping mappings and arrays other
than `bytes` and `string`, as the compiler's getter does. A struct with a
struct-typed member, or with no member to return, has no getter here, and
neither has a mapping whose key is neither an elementary value type nor bytes/string.

Constants of elementary value types, `string` and `bytes`, declared in the
contract, a base, a reached library or at file level are imported with their
values when reachable. Each elaborates to two
procedures without parameters that evaluate the value and convert it to the
declared type, one with checked and one with wrapping arithmetic; byte
sequences are copied to fresh memory. Every reference to the constant calls
the procedure of the arithmetic it is in, as the compiler's IR calls one of
two functions per constant, and a public constant's getter is the checked
one. So a value that overflows its type panics with `0x11` when it is
referenced in checked code, and wraps inside `unchecked`. References through
a contract name other than a library (`C.X`) are rejected. An operation over literals that the compiler types
as an integer (`10 ** 27`, `-1`) elaborates to that integer, as the compiler
folds it; one over other rational constants is still rejected. A number
literal the compiler takes as a fixed-size bytes (zero, or hex digits that
fill it, as in `bytes32 constant ROLE = 0x00`) stands for its big-endian
bytes, here and wherever a value is converted. String, hex and Unicode
literals also convert to `bytesN` when their byte length is at most N,
right-padded with zeros; longer literals are rejected.

Immutables of elementary value types, declared in the contract or a base, are
implemented, with getters for public ones. The source state holds a table of
their values, which a missing entry reads as zero. During creation an
immutable behaves like a zero-initialized variable: its inline initializer
runs in declaration order with the state variables' initializers, and the
constructor may read it and assign it, as the compiler allows. Creation
reserves 32 bytes of memory per immutable above the free-memory pointer, as
the compiler's creation code does, and `deploy_contract` returns the final
table; `call_contract` takes the table, which with the program stands for the
deployed code. The differential harness compares a creation's table with the
words the compiler's created code holds at its `immutableReferences` offsets,
and patches a call case's immutables into the runtime bytecode there.
Other immutables are rejected.

A contract or interface type is read as `address`, which is its value at
run time, stored and ABI encoded as one: in type names, in the type
identifiers of expressions and in storage layouts. `I(a)` is a conversion to
`address`, `this` is the contract's own address, and an external call
`c.f{value: v, gas: g}(args)` may name any contract-typed `c`; a gas option
caps the callee's gas as it does for `a.call`, below. `new C`, `type(C)`
other than `type(I).interfaceId` (below), external calls to getters and the
members of external functions other than `selector` (below) are rejected.
Nominal parameter type identifiers keep overloads distinct for `super`
lookup even when their runtime representations agree.

Enums, declared at file level, in a contract or in a library, are read by
their declaration id: type identifiers `t_enum$_E_$n` and storage-layout
types `t_enum(E)n` become `t_enum_n`. `E.A` is the constant of `A`'s index,
and `E(x)` and `uint8(e)` are conversions; converting an out-of-range value
panics with 0x21. An enum occupies one byte of storage; reading a stored
byte outside its member range fails closed with `InvalidCompletion`, even if
the value is never used. A `bool` storage byte other than 0 or 1 also fails
closed. The compiler can retain these non-canonical bytes on its stack, which
the core's source values cannot represent. An enum is
ABI encoded as `uint8`, as a parameter, a return, an event argument or an
external call's argument. A call or creation whose enum argument is out of
range reverts when the decoder reaches it, before later arguments are read.
`type(E).min` and `type(E).max` are the first and last enum values.
Enums as mapping keys, as elements of memory or calldata
arrays, as constants or immutables, or returned by an
external call are rejected.

`keccak256(b)` hashes the contents of a `bytes` value with Keccak-256, giving
a `bytes32`. A string or hex literal is hashed directly without allocating
memory. A `bytes` value in storage or calldata is copied to memory, as for
an internal call's argument.
`ecrecover(h, v, r, s)` is the address that the signature `(v, r, s)` of the
hash `h` recovers, or `address(0)` for an invalid signature, as the compiler's
call to the precompile at address 1 gives. Its arguments are converted to
`bytes32`, `uint8`, `bytes32` and `bytes32` as an internal call's are.
`f.selector`, `I.f.selector` and `E.selector` are constants: the selector the
compiler records on the function, error or event they name (four bytes, or 32
for an event), also of a library's public function or event, and
`this.x.selector` is that of a public state variable's getter. A contract
value in `x.f.selector` or `x.getter.selector` is evaluated first, including
its effects and failures; the selector still comes from the declaration.
`this`, contract, interface, library and module names need no evaluation.
`type(I).interfaceId` is the constant XOR of the selectors of the functions
the interface `I` declares itself, not those it inherits, nor its `fallback`
or `receive`; `I` must name an interface directly, not through a module, and
an abstract contract's `interfaceId` is rejected. A selector of any other
function-typed value is rejected, and so are `sha256` and `ripemd160`.

`c ? a : b` evaluates `c`, then only the operand it chooses, converted to the
type the compiler gives the whole expression, which must be a value type,
a memory reference or a tuple of supported component types (a memory operand
is the same reference, not a copy). Conditionals of storage, calldata or
function type are rejected.

`abi.encode`, `abi.encodePacked`, `abi.encodeWithSelector` and
`abi.encodeWithSignature` give a new memory `bytes`, allocated as the
compiler allocates it. Their arguments are evaluated in order and may be
scalars, byte sequences in any location, which are encoded where they are,
and string and hex literals; `abi.encode` also takes integer literals, encoded as
their smallest type, which has the encoding of `int256` or `uint256`.
`abi.encode` gives the standard ABI encoding of the arguments, after the four
bytes of a `bytes4` selector for `encodeWithSelector`, or of the Keccak-256
hash of a literal signature for `encodeWithSignature`; `abi.encodePacked`
gives each scalar in its own width, a `bytesN` as its N bytes, and a byte
sequence as its contents. Unpacked encoding also accepts fixed and dynamic
arrays of scalars, byte sequences and nested arrays in memory, calldata or
storage, retaining the reference until all arguments have been evaluated.
Packed arrays, structs as arguments, a selector that
is not a `bytes4` value (a literal selector included), and a signature that is
not a plain string literal are rejected.

`abi.encodeCall(f, (a, b))` gives `f`'s selector followed by the standard ABI
encoding of the arguments, each converted to its parameter's type as an
internal call's argument is; a single argument may stand without parentheses.
`f` is a member access naming a function whose receiver is one the compiler
does not evaluate (as for `x.f.selector`), or a variable other than a
constant, which is not read (reading it has no effect). Parameters must be
scalars or byte sequences; other receivers (a constant, whose initializer the
compiler evaluates and which may fail, included), and array and struct
parameters, are rejected.

`abi.decode(data, (T1, ..., Tk))` decodes a memory `bytes` into values of
elementary types (booleans, integers, addresses and fixed-size byte
sequences, including erased user-defined value types), as the compiler's
decoder from memory does. The result keeps the compiler's annotated types:
a plain `address` target decodes as `address payable`, while a user-defined
value type backed by nonpayable `address` keeps that underlying type.
Each result must match its requested elementary type or its payable-address
decoding variant. Data shorter than the
encoding, or a word that is not a value of its type, reverts with no data, and
data after the encoding is ignored. It allocates nothing. Data in calldata or
storage, and types other than elementary ones, are rejected.

`a.call(data)`, `a.staticcall(data)` and `a.delegatecall(data)`, with `a`
an address and `data` a memory or calldata `bytes` or a bytes literal,
evaluate `a`, then their call options `{value: v, gas: g}` in the order
written, then `data`, and call `a` with the bytes of `data` as its input,
giving the success flag and the return data. The data is passed where it is: a
literal or calldata is not copied into allocated memory. `call` sends `v` (0
without the option): a caller that cannot pay it fails the call without
running it, and sending value from a static frame is an `InvalidCompletion`.
`staticcall` makes a static call. `delegatecall` runs
`a`'s code as this contract, on its own storage and balance, with this call's
`msg.sender` and `msg.value`, and moves no value. The source does not track
gas: without a gas option the callee gets the same fixed budget a high-level
call gives it (`external_call_gas`), where the compiled code forwards all but
a 64th of what is left; with one, it gets `g` capped at that budget. A failed
call, the callee's revert included, gives `false` and leaves the caller's
state as it was; a call to an address without code succeeds with no data.
Return data is copied into a new memory `bytes`, allocated as the compiler
allocates it, and no return data gives the shared empty `bytes`, allocating
nothing. Data in storage is rejected.

`bytes.concat(...)` uses packed encoding of its byte sequences, fixed-size bytes
and literals. `string.concat(...)` concatenates strings and string literals.
Both allocate a fresh memory object, with the corresponding `bytes` or `string`
type, including the zero-argument and single-argument forms.

`address.code.length` reads the account's code size directly, including zero for
an account without code. The receiver is evaluated once and no memory bytes
object is allocated. Standalone `address.code` remains unsupported.
`address.balance` reads the account's current balance from the source world,
after evaluating its receiver once. Payable and nonpayable addresses use the
same lookup. `bytesN.length` evaluates its receiver and gives N as a `uint8`.
`address payable.transfer(value)` evaluates the receiver before the amount
and runs an empty-data value call with exactly the 2300 gas stipend. Failure
forwards the callee's revert bytes; success records its return bytes in the
frame's return-data buffer without allocating memory. Subsequent assembly
can read that buffer. A failed call or enclosing revert rolls back the transfer.

External calls returning scalar values admit `try ... returns (...) { ... }
catch (bytes memory reason) { ... }`. Only failure of the external call selects
the catch body; argument evaluation, missing-code checks, return decoding and
the success/catch bodies keep their ordinary failure behavior. Nonempty revert
data is copied into a fresh memory bytes object; empty data uses the default
empty bytes reference. Contract creation, typed `Error`/`Panic` handlers and
catch clauses without a bytes parameter remain unsupported.

Internal and private library functions, their modifiers, and library
constants come with the contracts that use them, also through each other,
from the functions calls can reach (an overridden function counts only when
a `super` or explicit base call may run it): `L.f(args)` is an internal call of `f`,
`x.f(args)`, with `f` attached to the type of `x` by `using L for T`, is one
with `x` as the first argument, evaluated before the others, and `L.c` names
the constant `c`. Library functions see no state variables. `using`
directives naming a library are accepted, in a contract or at file level,
since the compiler resolves which function a call names. A bound call whose
receiver is in storage or calldata and whose first parameter is in memory is
rejected: the compiler copies the receiver before evaluating the other
arguments, while elaboration converts arguments after evaluating them all.
Public and external library functions, which a contract calls with
`DELEGATECALL`, and library structs are rejected. Referenced library events
are imported with the contracts that emit them. Function-list
`using` directives are accepted: attached free and library functions use the
same internal-call path. In the Yul the compiler emits, `linkersymbol`, a linked
library's address, is not admitted.

User-defined value types declared at file, contract or library scope are
imported as their elementary underlying types, including nested mapping,
array and struct-field types and storage-layout annotations. `T.wrap` and
`T.unwrap` are scalar conversions, checked against the referenced declaration.
ABI signatures, event topics and error selectors use the compiler's underlying
types. Constants and reachable free functions accompany their callers; a
resolved user-defined operator is an internal call of its pure free function,
with operands evaluated left to right. Its checked arithmetic context belongs
to the callee. Raw parameter type identifiers are retained separately for
nominal `super` overload lookup after runtime type erasure.

Named arguments, `f({b: y, a: x})`, are implemented for internal, bound
library, `super` and external calls, `emit` and `revert` with a custom error.
As the compiler does, the arguments are evaluated in the call's order, then
passed in the parameters' order, each converted to its parameter's type; a
bound call's receiver comes first, as without names. The importer records,
for each parameter of the declaration the compiler resolved, the position of
its argument, and the checker requires a permutation of the argument
positions. Names on type conversions, `new`, `keccak256`, other builtins and
struct constructors are rejected.

Memory arrays of elementary leaves or byte sequences, nested to any depth, are
implemented: locals, parameters and returns, `new T[](n)`, `new bytes(n)` and
`new string(n)`, indexing, `.length`, and ABI decoding and encoding, with the
pinned compiler's layout (a length word before dynamic arrays' elements, none
for static ones) and checks: panic `0x41` for a length >= `2^64` or an
allocation past the memory limit, `0x32` for an index out of range, and the
decoder's order of revert and panic checks. A dynamic memory array's default
value is the shared empty array; a static one is allocated zeroed, with its
static rows allocated eagerly. Functions with modifiers and a static memory
array return are rejected: the compiler allocates that array once and passes it
through the modifiers, which the per-level procedures do not model.

Calldata arrays of the same element types, except fixed-size dimensions of
dynamic elements (`string[2]`, `uint256[][2]`), which import rejects, are
implemented as references into the frame's calldata: parameters, `T[] calldata` locals, indexing, `.length`,
copies to memory, and ABI encoding as return values and external call
arguments. Static arrays are read in place; dynamic elements are reached
through their offsets with the pinned compiler's checks, which revert, and an
index out of range panics with `0x32`. Elementary elements are validated when
read, so a dirty element reverts when it is indexed, copied or re-encoded.

Storage arrays of the same element types are values too: they copy to memory
(reading every element, panic `0x41` past the allocation limit), are assigned
from memory, calldata or another storage array, and are ABI-encoded in place as
return values and external call arguments. An assignment from another
array reads the source first, clears the destination (shrinking it, nested
data included) and writes the elements, converting them as the compiler's
implicit conversions allow (`uint8[]` to `uint16[]`, `bytes8` to `bytes10`,
static to dynamic, a static array into a longer static one, whose remaining
elements are cleared); a self-assignment returns at once, as the compiler's
copy does. Reading the whole source before clearing the destination differs from the
compiler, which resizes the destination and then copies slot by slot, only
under storage forged with inline assembly: two distinct arrays that alias
through a wrapped-around length, or which failure comes first when a corrupt
header meets malformed calldata. `T storage` locals of arrays are still
rejected.

Struct declarations may be file-level or contract members. User-defined type
names and field accesses retain declaration IDs; field ownership and expression
types are checked against the declared struct. Struct fields use solc's storage
pointer identifiers where state variables use storage reference identifiers.
The importer preserves that distinction and ignores only the display name
inside a struct type identifier, retaining its declaration ID and location.
`storageLayout.types` supplies each used struct's ordered members, relative
slots/offsets and size. Member IDs/types must match the declaration; sizes must
be positive multiples of a slot. Core layout checks reject fields outside the
struct's stride, scalar fields crossing a slot boundary, unaligned aggregates,
and cyclic inline containment. Layout calculation and byte disjointness remain
trusted compiler work. Unused declarations need no runtime layout.

The core program owns semantic struct declarations independently of keyed
storage layouts, including unused structs with no runtime layout. Its environment
is derived from both. Member navigation extends an already captured base, and
array strides use each struct's whole-slot size. Raw elaboration preserves
these declarations; the complete core checker rejects missing or inconsistent
runtime layouts as invalid generated core at the checked preparation boundary.

The importer validates `transientStorageLayout` alongside `storageLayout`,
preserving each table's order while interleaving their entries by declaration.

## Normalized AST

`syntax/solidityImportScript.sml` defines the second layer, and
`syntax/solidityImportLib.sml` imports it from an exporter artifact, failing
closed: an unknown node type, a missing required field or a construct outside
the admitted subset below is an import error (for a function body, the
function is kept unsupported; see Partial admission). The importer decodes
the compiler's string-valued kinds once, into datatypes: function kinds
(`function` and reachable `freeFunction` both become `FunctionKind`, plus
`receive`, `fallback` and `constructor`), visibilities, state mutabilities, address payability,
data locations, literal kinds and the
unary, binary and assignment operators. It also holds the one table of the
compiler's built-in declaration ids (`abi`, `msg`, `block`, `tx`, `this`,
`keccak256`, `ecrecover`, `addmod`, `mulmod`, `require`, `assert`, `revert`).
Transient state declarations carry a separate flag; `transient` on a local,
parameter or return declaration is rejected.
`tests/solidityImportTestScript.sml` holds the positive fixtures and negative
fixtures derived from them.

`valid_src_unit` checks what holds for the unit as a whole:

- each contract's node ids, with the unit's, are distinct, and the unit is
  among its compilation's source units;
- the contract's bases are distinct and start with the contract itself;
  contracts are scoped by the unit, functions by a base of their contract,
  structs by a base or a source unit of the compilation;
- function headers: parameters and returns of normalized types scoped by the
  function; library functions are
  internal or private `function`s scoped by a library distinct from the
  bases; modifier parameters likewise;
- every state variable has a normalized type and a type identifier agreeing
  with it; the storage layout lists the state variables in linearization
  order, bases first, each with its own type identifier;
- constants are of elementary value types or byte sequences, declared by a
  base or a library; event parameters are scoped by their event;
- initializers name state variables or immutables, base-constructor
  arguments name a constructor, and getters name a state variable, an
  immutable or a constant.

## Elaboration

`semantics/solidityElaborateScript.sml` elaborates a valid unit to
`core_program`; its header records the evaluation schedules, read from the
via-IR output in `testdata/frontend/expected/pure_core.json`.
`tests/solidityElaborateTestScript.sml` checks the elaborated fixture with
`wf_core_program` and runs it in the evaluator. The differential corpus runs
the same inputs, and a wider corpus of sources, through the deployed bytecode
in Verifereum and requires equal ABI-encoded outcomes; see
[differential-testing.md](differential-testing.md).

Admitted: one contract, flattened along its bases, with

- functions over elementary value types, persistent/transient value-type state
  variables and immutables, storage structs, value-type or bytes/string-key mappings and fixed or dynamic
  storage arrays; member and indexed scalar reads and updates, array lengths,
  scalar push and pop; bytes and string literals and memory or calldata
  values, which keep their locations (memory assignments alias,
  calldata-to-memory assignments copy); storage byte sequences and dynamic
  ABI values are rejected;
- locals, including tuple declarations with holes; simple and compound
  assignment to locals and state variables, tuple assignment, `++` and `--`;
- literals (no subdenominations), explicit elementary conversions (not
  `bytesN(b)` of a dynamic byte sequence `b`),
  `type(T).max` and `.min` of integer and enum types, unary, binary, comparison and
  short-circuit operators, conditional expressions over value types; an
  operation over literals that the compiler types as an integer is that
  integer, as the compiler folds it;
- `if`, `while`, `do`-`while`, `for`, `break`, `continue`, `return`,
  unchecked blocks, inline assembly over value-type locals, state-variable
  slots, storage pointer slots and offsets, value-type constants and memory `bytes` and `string` locals, with
  `call`, `staticcall` and their return data;
- internal calls with single or multiple returns, library calls (`L.f(args)`
  and `x.f(args)` through a using directive) and library constants (`L.c`),
  `super` and explicit base calls, external calls of contract types with
  `value` and `gas` options; low-level `call`, `staticcall` and `delegatecall`
  of addresses;
- `require`, `assert` and `revert` with boolean conditions and computed string
  messages; reads of `msg`, `tx` and `block` members and `address(this)`;
  emits of events with scalar, byte-sequence and array parameters (including
  indexed arrays), and reverts with custom errors with elementary, enum, string or bytes
  parameters; unsupported event parameter types reject the emitting function,
  leaving unrelated functions available; `keccak256`, `abi.encode*`, selectors;
- constants, state-variable initializers, constructors and base-constructor
  arguments (inheritance specifiers or constructor modifiers), which form one
  creation procedure.

Event arrays use their existing memory, calldata or storage references until
serialization, so later argument side effects are visible in the log. Data
uses standard ABI encoding. Indexed arrays hash concatenated element encodings
without array lengths or offsets; byte and string elements occupy padded words.
Storage byte/string padding is preserved as the pinned compiler copies it.

A contract or interface type is read as address, its value at run time,
stored and ABI encoded as one: in type names, type identifiers and storage
layouts, and as the target of a conversion `I(a)`. `this` is the contract's
own address.

Elaboration also checks each function body against the compiler's
annotations, at the node whose type it computes:

- every identifier resolves, within its lexical scope, to a variable whose
  type agrees with its annotation, or, as the callee of a call, to the most
  derived override of the function it names (`call_table`) or an internal
  library function; a pure function reads no state variable;
- calls have matching arity, ordered arguments and are annotated with the
  callee's return types; conversions are annotated with their target type,
  environment reads with their member's type; emits and reverts with an
  error carry as many arguments as the event or error has parameters;
- declaration statements are statements of a block or a `for` initializer,
  list exactly their declarations' ids, and are scoped by that block or
  `for`; returns name the enclosing function's return
  list; `break` and `continue` occur in loop bodies; conditions are boolean;
  modifier bodies make no super call, and modifier arguments see the
  function's parameters but not its return variables;
- a fallback takes no parameters and returns nothing, as the core's does;
- `delete` captures a scalar destination once and writes its default value,
  preserving neighboring packed storage. Aggregate deletion is rejected;
  every scalar result is annotated with its own type, and every other
  annotation decodes to an elementary, rational literal or tuple type.

Left to the compiler: storage layout calculation, that view functions write
no state variable, and the override metadata (which declarations each
function overrides, and that functions come most derived first).

## Partial admission

A contract is admitted per function. When a function's body or the body of
one of its modifiers falls outside the subset, or a fallback has parameters or
returns, import keeps the function with its header and the reason
(`fn_unsupported`) rather than rejecting the unit (a fallback with parameters
or returns keeps an empty body). Import goes on past what it cannot represent,
leaving a placeholder (`SrcUnsupportedTypeName`, `SrcUnsupportedExpr`,
`SrcUnsupportedStmt`) with the children it could import, so the reason has a
line for every unsupported node, each naming it. `solidityPrepareLib` then marks, until nothing changes,
every function that fails to elaborate, also by calling an unsupported one (by
an ordinary, `super` or explicit base call). The elaborator builds no
procedure for them and lists their ids in `core_program.unsupported_procedures`,
so their selectors, and receive, fallback or the constructor when unsupported,
still dispatch to them and an external call of one is invalid
(`call_contract_unsupported`), never a return or the fallback; it still
reverts first, as a supported one would, when it is sent value it does not
accept. An unsupported function never runs, so its `super` and base calls reach nothing:
a base function only they reach is neither checked nor elaborated. A constant
whose value does not elaborate, also by reading such a constant, has no
procedure either: its getter is listed as unsupported, and a function reading
it fails to elaborate. A modifier
whose body fails import keeps its header and its body with placeholders. The prepared unit
lists each function calls can reach, with its reason if unsupported.

What storage layout or dispatch depends on still rejects the whole unit
(`import_source_unit_blockers` gives the unit's blockers alongside the unit,
and `unit_rejections` lists the source checks it fails):
function headers (declaring base, kind, mutability, parameter and result
types; a library function must be an internal or private `function`),
modifier parameters and `virtual` modifiers, state variables, constant
declarations, bases
and their linearization, using directives, and a core program that fails
`wf_core_program`. A core program needs an entry procedure, so a unit whose
lowering has no procedure at all (no supported function, getter, library
function or constant procedure, and an unsupported constructor) is rejected
whole too, without the constructor's reason.

## Built-in failures

The pinned compiler represents `require`, `assert` and built-in `revert` as
ordinary calls with declaration references `-18`, `-3` and `-19`. Import maps
those references to `SrcBuiltinCall`; identifier spelling does not select a
built-in, so user declarations with those names remain internal calls.
Normalized checking admits `require(bool)`, `require(bool, string)`,
`require(bool, CustomError(...))`, `assert(bool)`, `revert()` and
`revert(string)`. String messages may be computed, or memory, calldata or
storage references. Literals are read from `hexValue` to preserve exact bytes,
including UTF-8 and NULs.

Elaboration evaluates the condition first, then every message or custom-error
argument in source order, including when `require` succeeds. Named custom-error
arguments are reordered to parameter order after evaluation. A successful
condition can therefore still propagate a panic or revert from an argument.
Only payload serialization and the built-in failure are conditional. This is
the pinned compiler's via-IR evaluation schedule.

A failed assertion emits `PanicCompletion 1`; bare require/revert emit empty
revert bytes. String messages use ABI `Error(string)` with selector `08c379a0`.
Custom errors use their four-byte selector followed by the ABI encoding of
their elementary, enum, `string` or `bytes` arguments. Both use runtime ABI
serialization, reading byte references directly from memory, calldata or
storage without allocating a copy. Later arguments can mutate those contents
before serialization. Storage header validation occurs only when serialized,
so a successful require does not inspect a corrupt storage message's header.
Existing internal-call propagation preserves the failure, and the source-frame
boundary rolls back earlier writes.

## Required validation

Before elaboration, a well-formed imported program should at least establish:

- uniqueness and kind-correct resolution of declaration IDs;
- valid source-unit and scope references;
- structurally normalized types and explicit data locations where required;
- consistency between type nodes, type descriptions, and referenced
  declarations;
- resolved ordinary calls and explicitly classified builtin operations;
- arity and argument-name consistency;
- valid assignment targets and declaration-assignment links;
- complete contract linearization and dispatch metadata when those features are
  admitted; and
- complete, declaration-consistent storage layout metadata for storage-using
  contracts.

Anything outside the admitted node and annotation vocabulary must produce an
import error, which rejects the unit or, inside a function's body or a
modifier, marks the function unsupported (see Partial admission), never a
partial semantic result.

## Open reconnaissance work

Before fixing a complete core AST, extend the corpus to cover control flow,
tuple holes, modifiers, external calls, creation,
try/catch, errors, fallback/receive, dynamic and memory/calldata arrays, bytes/string, and function
pointers. Transient value types and custom storage bases have differential fixtures.
The first HOL type
theory can begin from the normalized types already observed, provided unsupported
forms continue to fail closed.

## Tuple expressions and assignments

Tuple literals and conditional tuple results use the existing product values.
Conditional components convert to the conditional expression's annotated types;
only the selected branch runs. Destructuring supports the same destinations as
ordinary assignment, including storage members, indexed storage locations and
memory elements. It first evaluates and snapshots the right-hand values, then
evaluates left-hand operands from left to right, then writes from right to left.
Storage navigation checks bounds during operand evaluation; memory indices are
saved and bounds-checked at each write. Holes consume a value without
capturing a location. Repeated destinations therefore retain the leftmost
assigned component.

Scalar and tuple conditional joins bind the selected memory reference without
allocating a default object. Their temporary references cannot be read as fixed
arrays before assignment; declarations of fixed memory arrays still allocate
their normal zero-filled objects.
