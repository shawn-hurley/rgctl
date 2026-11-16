# Declaration-qualified environment flow

`ParsedSourceFile::environment_facts` indexes source bindings through the already
cached native tree and links separately lowered procedures. Its inputs must be
from the same immutable source revision. The origin query consumes typed facts;
it does not parse source or scan unrelated repositories.

## Records and identity

`EnvironmentBinding` identifies the owning procedure/module UUID and canonical
source declaration span. Reads and stores join by this identity, never by a
repository-wide bare-name match. Lexical scope spans distinguish shadowed
bindings. Parameters are producers; module/package initializers and explicit
assignments supply possible values. Ordinary local reaching definitions stay
authoritative unless a binding crosses a procedure boundary or represents a
separately lowered callable definition value.

`EnvironmentTransfer` connects an exact function-qualified producer and read.
`EnvironmentMemberRead` resolves a bare Java member to its receiver and member
load. `EnvironmentCallable` connects a literal/definition expression to a
canonical separately prepared body. This restores function-value production for
closures without lowering their bodies into their enclosing CFG.

`OriginAnalysis::build_with_environment` combines `OriginInputs` with these
facts and emits `OriginTransferCause::Environment` provenance. Explicit member
loads reuse the existing object-origin/member store. Canonical callable literals
feed the existing callable-value worklist and invocation binder.

## Module initialization and imports

`build_module_cfg` reuses the parsed tree to lower one module/package procedure.
It skips declared callable and class bodies, including function literals within
initializers. Those declarations are values, not ordinary execution edges into
their bodies. Module UUIDs are query-local identities supplied by the caller;
module records do not become invented persisted graph functions.

`EnvironmentExport` retains module declarations and their explicit possible
producers. `EnvironmentExternalRead` describes named imports, selected namespace
members or same-package Go reads. `link_environment_modules` resolves against
repository-relative source-module paths. Direct relative JS/TS imports, Python
source-module imports and directory/package-qualified Go state are supported.
Resolved module choices are cached during linking. Unrelated modules with equal
export names do not share bindings.

An unresolved external package, missing export or absent source producer is
coverage evidence. Source-package resolution is deliberately restricted: Go
external module prefixes require a canonical package map; arbitrary import
hooks, wildcard imports, re-exports, namespace-object aliases, import-rebinding
semantics and imported class/function aliases without an exported producer need
further qualification. Existing nominal-symbol candidates may still contribute
conservative warnings; that does not qualify those environment paths.

## Capture and update policy

Captured bindings retain possible writes, including writes after closure
creation and supported Python `nonlocal` updates. Escaped closures keep their
owning binding. This first solver merges invocation/environment instances and
weakly retains alternatives; it does not prove precise closure-instance or
capture-time exclusions. Language constructs outside the tested declaration and
scope forms remain partial. Python class members are not ordinary method lexical
locals; Java implicit instance members use receiver-qualified loads instead.

## Additional operand repairs

Java `field_access` now lowers to member reads/stores. Bare Java member reads can
join the same instance state through `EnvironmentMemberRead`. JS/TS object literal
values use aggregate storage, and callable definitions/literals retain an outer
expression identity while their bodies remain separate. `TypeApplication`
preserves a generic constructor's nominal head without treating type arguments as
that constructor value. These persisted semantics require CFG version 11 and
RBCP v14; previous records invalidate through existing revision guards.

## Bounds, missing facts and consumers

Indexing has syntax-node, declaration and candidate/link limits. Program linking
caps transfers and metadata; the origin solver retains its function, fact,
transfer and work budgets. Missing bindings, producers, receivers or callable
bodies and exhausted budgets remain explicit diagnostics. No process RSS or
repository-scale performance guarantee is inferred from these count bounds.

A function literal lacking a prepared canonical graph callable produces
`MissingCallableDefinition`; the adapter must not invent a target to hide that
extraction gap. Go anonymous registry factories currently exercise this case.
Generated constructors, implicit descriptors/`__call__`, decorator replacement,
partial argument prefixes and reflection remain separate models.

These are value-transfer facts usable by shared native dependence consumers.
The dependency-impact adapter currently uses them to improve possible receiver
and callable targets. All scalar state dependences are not thereby converted
into caller/callee paths, and interprocedural taint consumption remains separate
work. Empty paths with partial coverage cannot certify upgrade safety.

## Validation

Native regressions cover four-language module state, captures without fallback,
late writes, nonlocal writes, escaped closures, shadowing, generic constructor
identity, Java members, source-import/package linking, unrelated-module isolation,
module body separation and explicit limits. Runtime qualification also exercises
controlled before/after source variants and the full impact catalog.
