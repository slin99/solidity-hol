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
function's `baseFunctions`. Base-constructor specifiers on constructors
(`constructors.sol`) and invocations of non-virtual modifiers
(`modifiers.sol`) are resolved through their `referencedDeclaration`; virtual
and overriding modifiers are rejected. A `super.f(...)` call
(`super_calls.sol`) runs what the compiler's lookup finds in the deployed
contract's linearization: the first function after the caller's contract with
the name and parameter types of the declaration the call's
`referencedDeclaration` names. That declaration is resolved from the caller's
own contract, so in a diamond it can differ from the function that runs. The
overridden functions super calls reach are checked and elaborated, but not
dispatched. `super` in a modifier body, an initializer or a base-constructor
argument is rejected.

## Storage layout

`storageLayout` is separate from the AST. It contains state-variable entries
with declaration IDs, slots, byte offsets, contract names, and references into a
layout type table. Type-table entries describe encodings such as `inplace`,
`mapping`, and `dynamic_array`, byte widths, member offsets, keys, values, and
base element types.

Source types and layout descriptors must remain separate formal structures. The
compiler initially supplies layout calculation; Solidity-HOL interprets the
layout when reading, writing, and capturing references. The declaration IDs in
layout entries must resolve to compatible state-variable declarations.

Storage declarations now include elementary scalars, structs, scalar-key
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
are checked against the normalized type. The scalar leaf width determines
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
neither has a mapping whose key is not an elementary value type.

Constants of elementary value types, `string` and `bytes`, declared in the
contract or a base, are imported with their values. Each elaborates to two
procedures without parameters that evaluate the value and convert it to the
declared type, one with checked and one with wrapping arithmetic; byte
sequences are copied to fresh memory. Every reference to the constant calls
the procedure of the arithmetic it is in, as the compiler's IR calls one of
two functions per constant, and a public constant's getter is the checked
one. So a value that overflows its type panics with `0x11` when it is
referenced in checked code, and wraps inside `unchecked`. File-level constants and references through a contract name
other than a library (`C.X`) are rejected. An operation over literals that the compiler types
as an integer (`10 ** 27`, `-1`) elaborates to that integer, as the compiler
folds it; one over other rational constants is still rejected. A number
literal the compiler takes as a fixed-size bytes (zero, or hex digits that
fill it, as in `bytes32 constant ROLE = 0x00`) stands for its big-endian
bytes, here and wherever a value is converted.

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
`c.f{value: v}(args)` may name any contract-typed `c`. `new C`, `type(C)`
other than `type(I).interfaceId` (below), external calls to getters and the
members of external functions other than `selector` (below) are rejected, as
are overloads that differ only in contract-typed parameters, which reading
them as `address` would merge.

Enums, declared at file level, in a contract or in a library, are read by
their declaration id: type identifiers `t_enum$_E_$n` and storage-layout
types `t_enum(E)n` become `t_enum_n`. `E.A` is the constant of `A`'s index,
and `E(x)` and `uint8(e)` are conversions; converting an out-of-range value
panics with 0x21. An enum occupies one byte of storage; reading a stored
byte that is out of range panics with 0x21 when it is read, where the
compiler checks it only where the value is used. It is
ABI encoded as `uint8`, as a parameter, a return, an event argument or an
external call's argument. A call or creation whose enum argument is out of
range reverts when the decoder reaches it, before later arguments are read. Enums as mapping keys, as elements of memory or calldata
arrays, as constants, immutables or error parameters, returned by an
external call, `type(E).min/max` and `delete` are rejected.

`keccak256(b)` hashes the contents of a `bytes` value with Keccak-256, giving
a `bytes32`. A literal argument is first made a memory `bytes`, and one in
storage or calldata is copied to memory, as for an internal call's argument.
`f.selector`, `I.f.selector` and `E.selector` are constants: the selector the
compiler records on the function, error or event they name (four bytes, or 32
for an event), also of a library's public function or event, and
`this.x.selector` is that of a public state variable's getter. The receiver in
`x.f.selector` must be `this`, a contract, interface or library name,
possibly qualified by imported modules (`M.I.f.selector`), or an imported
module (`M.E.selector`), none of which the compiler evaluates.
`type(I).interfaceId` is the constant XOR of the selectors of the functions
the interface `I` declares itself, not those it inherits, nor its `fallback`
or `receive`; `I` must name an interface directly, not through a module, and
an abstract contract's `interfaceId` is rejected. A selector of any other
function-typed value is rejected, and so are `sha256`, `ripemd160`,
`ecrecover` and `abi.decode`.

`c ? a : b` evaluates `c`, then only the operand it chooses, converted to the
type the compiler gives the whole expression, which must be a value type or
a memory reference (a memory operand is the same reference, not a copy).
Conditionals of tuple, storage, calldata or function type are rejected.

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
sequence as its contents. Arrays and structs as arguments, a selector that
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

`bytes.concat(...)` uses packed encoding of its byte sequences, fixed-size bytes
and literals. `string.concat(...)` concatenates strings and string literals.
Both allocate a fresh memory object, with the corresponding `bytes` or `string`
type, including the zero-argument and single-argument forms.

`address.code.length` reads the account's code size directly, including zero for
an account without code. The receiver is evaluated once and no memory bytes
object is allocated. Standalone `address.code` remains unsupported.

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
a super call may run it): `L.f(args)` is an internal call of `f`,
`x.f(args)`, with `f` attached to the type of `x` by `using L for T`, is one
with `x` as the first argument, evaluated before the others, and `L.c` names
the constant `c`. Library functions see no state variables. `using`
directives naming a library are accepted, in a contract or at file level,
since the compiler resolves which function a call names. A bound call whose
receiver is in storage or calldata and whose first parameter is in memory is
rejected: the compiler copies the receiver before evaluating the other
arguments, while elaboration converts arguments after evaluating them all.
Public and external library functions, which a contract calls with
`DELEGATECALL`, every `using {f, ...} for T` with a function list (library
functions included) and user-defined operators, and library structs and
events are rejected; a file-level directive with a function list rejects the
compilation, whichever file it is in. In the Yul the compiler emits, `linkersymbol`, a linked
library's address, is not admitted.

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

The selected compiler also emits `transientStorageLayout`. It is empty for the
initial corpus, so transient layout remains unvalidated.

## Normalized AST

`syntax/solidityImportScript.sml` defines the second layer, and
`syntax/solidityImportLib.sml` imports it from an exporter artifact, failing
closed: an unknown node type, a missing required field or a construct outside
the admitted subset below is an import error (for a function body, the
function is kept unsupported; see Partial admission).
`tests/solidityImportTestScript.sml` holds the positive fixtures and negative
fixtures derived from them.

`valid_src_unit` checks what holds for the unit as a whole:

- each contract's node ids, with the unit's, are distinct, and the unit is
  among its compilation's source units;
- the contract's bases are distinct and start with the contract itself;
  contracts are scoped by the unit, functions by a base of their contract,
  structs by a base or a source unit of the compilation;
- function headers: kind (`function`, `receive`, `fallback`, `constructor`),
  mutability (`pure`, `view`, `nonpayable`, `payable`), and parameters and
  returns of normalized types scoped by the function; library functions are
  internal or private `function`s scoped by a library distinct from the
  bases; modifier parameters likewise;
- every state variable has a normalized type and a type identifier agreeing
  with it; the storage layout lists the state variables in linearization
  order, bases first, each with its own type identifier;
- constants are of elementary value types or byte sequences, declared by a
  base or a library; event parameters are elementary, scoped by their event;
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

- functions over elementary value types, value-type state variables and
  immutables, storage structs, scalar-key mappings and fixed or dynamic
  storage arrays; member and indexed scalar reads and updates, array lengths,
  scalar push and pop; bytes and string literals and memory or calldata
  values, which keep their locations (memory assignments alias,
  calldata-to-memory assignments copy); storage byte sequences and dynamic
  ABI values are rejected;
- locals, including tuple declarations with holes; simple and compound
  assignment to locals and state variables, tuple assignment, `++` and `--`;
- literals (no subdenominations), explicit elementary conversions,
  `type(T).max` and `.min` of integer types, unary, binary, comparison and
  short-circuit operators, conditional expressions over value types; an
  operation over literals that the compiler types as an integer is that
  integer, as the compiler folds it;
- `if`, `while`, `do`-`while`, `for`, `break`, `continue`, `return`,
  unchecked blocks, inline assembly over locals and state-variable slots;
- internal calls with single or multiple returns, library calls (`L.f(args)`
  and `x.f(args)` through a using directive) and library constants (`L.c`),
  `super` in calls, external calls of contract types;
- `require`, `assert` and `revert` with boolean conditions and literal string
  messages; reads of `msg`, `tx` and `block` members and `address(this)`;
  emits of events and reverts with custom errors, both with elementary
  parameters; `keccak256`, `abi.encode*`, selectors;
- constants, state-variable initializers, constructors and base-constructor
  arguments (inheritance specifiers or constructor modifiers), which form one
  creation procedure.

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
- operators belong to the admitted set; every scalar result is annotated with
  its own type, and every other annotation decodes to an elementary, rational
  literal or tuple type.

Left to the compiler: storage layout calculation, that view functions write
no state variable, and the override metadata (which declarations each
function overrides, and that functions come most derived first).

## Partial admission

A contract is admitted per function. When a function's body or the body of
one of its modifiers falls outside the subset, import keeps the function with
its header, an empty body and the reason (`fn_unsupported`) rather than
rejecting the unit. `solidityPrepareLib` then marks, until nothing changes,
every function that fails to elaborate, also by calling an unsupported one (by
a call or a super call). The elaborator builds no
procedure for them and lists their ids in `core_program.unsupported_procedures`,
so their selectors, and receive, fallback or the constructor when unsupported,
still dispatch to them and an external call of one is invalid
(`call_contract_unsupported`), never a return or the fallback; it still
reverts first, as a supported one would, when it is sent value it does not
accept. An unsupported function never runs, so its super calls reach nothing:
a base function only they reach is neither checked nor elaborated. A modifier
whose body fails import keeps its header with an empty body. The prepared unit
lists each function calls can reach, with its reason if unsupported.

What storage layout or dispatch depends on still rejects the whole unit:
function headers (declaring base, kind, mutability, parameter and result
types; a library function must be an internal or private `function`),
modifier parameters and `virtual` modifiers, state variables, constants, bases
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
Normalized checking admits `require(bool)`, `require(bool, literal)`,
`assert(bool)`, `revert()` and `revert(literal)`. Messages are string, Unicode
string or string-compatible hex literals, read from `hexValue` to preserve
exact bytes, including UTF-8 and NULs.

Elaboration evaluates the condition before selecting the success/failure
branch. A failed assertion emits `PanicCompletion 1`; bare require/revert emit
empty revert bytes. Literal messages use ABI `Error(string)` with selector
`08c379a0`, offset 32, byte length and zero padding to a multiple of 32 bytes.
Existing internal-call propagation preserves the failure and the source-frame
boundary rolls back all earlier writes. Literal messages have no evaluation
effects. Dynamic message expressions remain rejected, including on a successful
require; future string support must evaluate them on both paths according to
the compiler profile's argument schedule. A revert with a custom error,
`revert E(args)`, reverts with the error's 4-byte selector followed by the ABI
encoding of its arguments, which must be of elementary types.

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
try/catch, errors, fallback/receive, dynamic and memory/calldata arrays, bytes/string, function
pointers, transient storage, and custom storage layout bases. The first HOL type
theory can begin from the normalized types already observed, provided unsupported
forms continue to fail closed.
