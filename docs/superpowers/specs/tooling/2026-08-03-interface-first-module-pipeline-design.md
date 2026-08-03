# Interface-first module and import pipeline — Design

**Date:** 2026-08-03  
**Status:** Proposed; implementation target after nominal `String` and JSON stabilization  
**Topic:** canonical modules, imports, interfaces, dependencies, and emission

## 1. Decision

Cure compilation SHALL be interface-first. Parsing, name resolution,
elaboration, totality, reachability, and code generation SHALL resolve Cure
modules and definitions through compiler-owned canonical module interfaces.
They SHALL NOT discover semantic dependencies by probing the currently loaded
BEAM code path.

`use` has one language meaning: it introduces selected exported names into the
consumer's lexical scope. It is not a source-file scheduling directive.

Qualified access has a separate meaning:

```cure
Std.String.characters(value)
```

resolves `Std.String` through the compilation universe's module index and
`characters` through that module's checked interface. It does not expose bare
`characters`, and it does not require `Cure.Std.String` to have been emitted or
loaded as a BEAM module.

Ambient prelude availability is compiler policy over the same interface table.
It is not implemented by copying imports into every source file.

## 2. Why the current pipeline is unsound

The 2026-07-08 auto-import-order design separated dependencies into:

- order edges, consisting principally of `use`; and
- closure edges, including qualified references and prelude providers.

It declared qualified references and the dependent pipeline order-independent,
but retained code paths whose resolution or emission required already-loaded
BEAM modules. These two properties cannot coexist. If compilation needs a
dependency BEAM, that dependency is order-sensitive whether or not its source
spells `use`.

Nominal `String` supplied the minimal counterexample. The graph scheduled
`Std.Regex.Syntax.Model` before `Std.String` because the former used ambient
`String` without `use Std.String`. This had been accidentally harmless while
`String` was a transparent `List(Char)` alias. Once `String` became a nominal
record, it became a real semantic and runtime dependency. Failure to emit the
provider was later reported as repeated `missing_stdlib_module` failures in its
consumers, obscuring the original error.

Adding ordering-only `use` declarations would encode a compiler implementation
detail in user source and would fail again for macro-generated qualified calls,
ambient protocols, transitive interface references, and future representation
changes.

This design supersedes the following claims in the 2026-07-08 design:

- that qualified references require no compiler dependency ordering;
- that dependent compilation is independent of module-interface availability;
- that SCC members may always be compiled in arbitrary alphabetical order;
- that loading emitted BEAMs during a pass is an acceptable semantic resolver.

DepGraph scanning, deterministic ordering, duplicate detection, artifact
closure, and the distinction between lexical visibility and dependency
availability remain useful and are retained under the stronger model below.

## 3. Evidence from other compilers

The design follows common compiler boundaries rather than copying one language
wholesale.

- **Swift:** all files in a module are visible to the frontend even when
  separate primary-file jobs emit separate object files. External declarations
  are obtained from serialized module interfaces. Job partitioning is not
  language-visible file order.
- **Rust:** a crate-wide module graph is built before staged name resolution.
  `use` creates lexical bindings; declaration order does not schedule files.
  Expansion-time resolutions are validated after expansion so macro order does
  not change identity.
- **Zig:** declarations, including declarations in imported files, are analyzed
  on demand and are explicitly order-independent. Cure adopts demand-driven
  body/interface loading, but not Zig's unchecked top-level model.
- **Idris 2:** imported modules contribute checked interfaces, while backend
  code generation receives a compiler-owned global definition context. Its
  backend does not reconstruct dependent semantics from host-language modules.
- **Elixir:** the parallel compiler waits when a file needs a module another
  compiler process is producing. Cure adopts this only for final artifact work;
  BEAM availability is too late to serve as Cure's semantic interface.

Primary references:

- <https://download.swift.org/docs/assets/generics.pdf>
- <https://doc.rust-lang.org/reference/names/name-resolution.html>
- <https://doc.rust-lang.org/reference/items/use-declarations.html>
- <https://ziglang.org/documentation/master/>
- <https://idris2.readthedocs.io/en/latest/tutorial/modules.html>
- <https://github.com/idris-lang/Idris2/blob/master/docs/source/backends/backend-cookbook.rst>
- <https://hexdocs.pm/elixir/Kernel.ParallelCompiler.html>

## 4. Terminology and identities

### 4.1 Compilation universe

A **compilation universe** is the complete set of source modules, compiler-owned
modules, package interfaces, and the selected standard-library interface set
available to one invocation. Every bulk entry point constructs one universe:

- stdlib compilation;
- project and incremental compilation;
- tests and integration fixtures;
- bundle and escript construction;
- REPL sessions;
- documentation examples; and
- macro compilation and fallback evaluation.

No entry point may independently invent a smaller name-resolution model.

### 4.2 Canonical module identity

The declared module name is its identity. A source path is provenance and an
index key, not semantic identity.

```text
ModuleName = "Std.String"
DefinitionKey = :"Std.String#characters"
```

Filenames do not contribute to either identity. Duplicate providers for one
canonical module name are rejected before body elaboration.

### 4.3 Module skeleton and checked interface

A **module skeleton** is the early, possibly unelaborated declaration index
needed to break source-order dependence. It contains canonical declaration
names, declaration classes, visibility, source locations, fixities, macro
headers, and surface signatures where present. A skeleton is not usable as a
checked type.

A **checked module interface** contains the semantic information consumers may
use:

```text
ModuleInterface = {
  schema_version,
  module_name,
  source_path,
  source_hash,
  interface_hash,
  dependency_interface_hashes,
  direct_edges,
  owned_declarations,
  exported_declarations,
  canonical_externs,
  type_families,
  constructors,
  aliases,
  interfaces_and_implementations,
  macro_exports,
  required_compiletime_bodies,
  extension_payloads,
  source_metadata
}
```

The interface contains bodies only where consumer checking requires reduction:
transparent aliases, type-level functions, relevant proofs, inline compile-time
definitions, interface defaults, and macro expanders. Ordinary runtime bodies
remain in the owned checked module and runtime artifact.

## 5. Visibility is not availability

Every environment maintains distinct projections.

### 5.1 Qualified availability

A module is qualified-available when its canonical interface is present in the
compilation universe and the source or expansion contains an allowed direct
reference to it. Loading that interface adds no bare names.

```cure
Std.List.map(f, values)  # qualified lookup only
```

Transitive dependencies are loadable for checking canonical Core references,
hash validation, and packaging, but do not thereby become authored qualified
or bare scope. A source cannot obtain arbitrary namespace access merely because
one of its dependencies internally uses that namespace.

### 5.2 Lexical visibility

Bare candidates come only from:

1. local declarations and binders;
2. explicit `use` declarations, including their eventual `exposing` surface;
3. the ambient prelude policy; and
4. hygienic definition-site bindings explicitly carried by macro output.

`use M` exposes names owned and exported by `M`. It does not expose names that
`M` itself imported. Direct imports may participate in lexical preference;
qualified availability and transitive closure may not.

### 5.3 Prelude providers

Prelude providers are selected once from the canonical module index. Their
exported prelude surface is merged into the ambient lexical layer from a single
source of truth. The prelude merge:

- is idempotent;
- does not mark every provider as a direct import;
- does not allow one provider's private/direct imports to leak;
- preserves canonical identities under every merge order; and
- records semantic dependency edges for every actually consumed prelude name.

The last rule prevents the nominal-`String` failure without requiring a
synthetic `use Std.String` in every consumer.

## 6. One resolution boundary

All authored and generated syntax uses the same resolver API:

```text
resolve_bare(scope, name, namespace)
  -> canonical declaration | ambiguous candidates | missing

resolve_qualified(module_table, requesting_module, path, namespace)
  -> canonical declaration | unavailable module | missing export
```

The namespace argument distinguishes types, constructors, values, interfaces,
operators, and macros. Expected-type context may choose between a same-named
record family and value constructor, but both results are canonical.

The following may not bypass this boundary:

- macro output;
- derive output;
- lifted `where` helpers and lambdas;
- implementation methods and dictionaries;
- totality/reachability reconstruction;
- code generation; or
- REPL-generated declarations.

`macro_home_source` remains provenance for hygiene, expansion traces, and
locating the expander interface. It is not a dependency-resolution bridge.

## 7. Two graphs, not one overloaded graph

One static source scan cannot know every dependency because macros generate
declarations and type-directed elaboration selects implementations. Conversely,
the compiler needs some dependencies before it can expand or elaborate. Cure
therefore maintains two related graphs.

### 7.1 Bootstrap discovery graph

Built from headless parsing plus package/compiler metadata. It records enough
to start compilation:

```text
use_import
qualified_reference
declared_prelude_provider
macro_reference
compiler_owned_provider
package_dependency
```

This graph locates candidate interfaces, detects missing/duplicate modules, and
orders macro/interface prerequisites. It is conservative and may over-include.
It is never authoritative for final reachability or invalidation.

### 7.2 Checked semantic graph

Built as expansion and elaboration resolve canonical declarations. It records
actual semantic edges:

```text
lexical_use
qualified_reference
prelude_symbol_use
type_reference
value_reference
interface_provider
implementation_selection
macro_home
macro_generated_reference
generated_declaration_owner
extern_owner
runtime_call
```

Each edge stores the source module, target module and canonical declaration
where applicable, phase, provenance/span, and whether it affects:

- lexical scope;
- interface checking;
- compile-time execution;
- runtime emission;
- invalidation; and
- packaging.

This graph is authoritative for dependency hashes, totality, emission closure,
artifacts, and diagnostics.

### 7.3 Reconciliation

After each macro-expansion/publication round, newly generated module references
are resolved and added. Expansion continues to a stable syntax/interface set.
The final checked graph must be a subgraph of the resolved universe, though it
need not be a subgraph of the initial conservative edge set.

A generated qualified call requests an interface through the same module table;
it never causes the compiler to manufacture a `use` declaration.

## 8. Compilation phases

Every compilation entry point uses these phases.

### Phase A — Discover

1. Resolve source roots, package interfaces, stdlib interfaces, and
   compiler-owned modules.
2. Parse module headers, fixities, imports, qualified paths, decorators, macro
   references, and declaration headers.
3. Build the canonical `ModuleIndex` and module skeletons.
4. Reject duplicate identities and statically missing modules.

No Cure BEAM is loaded to answer a language-level lookup.

### Phase B — Expand and publish

1. Load or check macro-provider interfaces.
2. Expand recursively inside-out.
3. Predeclare generated names under their owning module.
4. Resolve generated references through the canonical resolver.
5. Repeat until no expansion publishes new declarations or dependencies.

Non-convergence and compile-time dependency cycles are diagnosed with the
expansion path.

### Phase C — Check interfaces

1. Predeclare every family, constructor, signature, implementation head,
   extern, and required reducible definition in an SCC.
2. Elaborate signatures and interface-required bodies against skeletons and
   already checked external interfaces.
3. Kernel-check and totality-check every published interface term that requires
   certification.
4. Freeze immutable `ModuleInterface` values.

No consumer receives a partially checked export environment.

### Phase D — Check bodies

Elaborate ordinary bodies against frozen interfaces and the module's owned
environment. Record canonical semantic edges as resolution occurs. Run
coverage, quantity, totality, proof-closure, and TCB gates over canonical keys.

Body elaboration is declaration-order independent. Demand-driven checking may
avoid unreachable ordinary bodies where the language mode permits, but public
interfaces and all requested roots are always checked.

### Phase E — Validate closure

Build a typed emission closure:

```text
ClosureEntry = definition(key, body, owner, origin)
             | extern(key, owner, target, origin)
```

Every reachable Core global must resolve to a checked body, a certified
compile-time-only definition that is erased, or a legitimate extern. Missing
entries report the originating Core reference and predecessor path.

### Phase F — Emit and publish

Emit BEAM modules from checked Core and symbolic canonical remote references.
Emission does not ask `Code.ensure_loaded?`, `module_info(:exports)`, or the code
server to resolve Cure definitions.

Artifact production may be parallel. A job may wait for another job's artifact
when packaging or host verification genuinely requires bytes, as Elixir's
parallel compiler does, but this wait cannot change name resolution or types.
Publish the complete artifact generation atomically only after every claimed
module and hash validates.

## 9. Cycles

Cycles are classified by phase rather than uniformly accepted or rejected.

### 9.1 Runtime cycles

Mutual remote calls between checked modules are legal. BEAM remote references
are symbolic, so neither module needs to be loaded while the other is emitted.

### 9.2 Interface cycles

An interface SCC is processed as a group:

1. collect and canonicalize all member skeletons;
2. predeclare every member export;
3. elaborate signatures and required reducible bodies against the group;
4. solve/check postponed constraints;
5. freeze the group only when all members validate.

Cycles that require an unavailable value before it can be checked, violate
universe/positivity/termination rules, or fail to reach a stable expansion are
rejected with the full canonical cycle and triggering declarations. Alphabetical
intra-SCC compilation is not a semantic solution.

### 9.3 Macro and compile-time execution cycles

A macro provider may depend on checked interfaces, but a cycle requiring an
expander to run before its own interface can exist is rejected. The diagnostic
distinguishes this from a legal runtime cycle.

### 9.4 Hashes for SCCs

`interface_hash` describes a module's own normalized semantic interface and
does not recursively embed dependency hashes. Dependency hashes are validation
metadata. For an SCC, incremental validation uses a component digest over the
sorted `(module_name, interface_hash)` members plus external dependency hashes.
This avoids an impossible cryptographic fixed point.

## 10. Incremental compilation

The cache key for an acyclic module is derived from:

```text
compiler schema and toolchain
canonical module identity
source hash
macro/expansion inputs
external checked-interface hashes
relevant compilation options
```

For an SCC, the source and expansion inputs of all members plus the component
digest form one invalidation unit. A source-only change that leaves the
normalized interface unchanged rebuilds that module's body/artifact but need
not invalidate semantic consumers. A changed interface invalidates consumers
through the checked graph.

Loading the same interface twice with identical keys returns the same immutable
semantic value and cannot duplicate aliases, implementations, or lexical
bindings.

## 11. Diagnostics

The pipeline reports the earliest causal failure once.

- Missing module diagnostics name the authored/generated reference and searched
  universe before body elaboration where possible.
- Interface failure names the provider, declaration, source span, expected and
  inferred Core types, and dependency path.
- A consumer whose provider already failed receives a compact dependent note,
  not a second `missing_stdlib_module` internal error.
- Cycle diagnostics name the cycle class, phase, canonical modules,
  declarations, and source locations.
- Emission never raises an uncontextualized `no such definition` or
  `ArgumentError`.
- Macro diagnostics preserve expansion provenance without using provenance to
  alter resolution.

`E101` is reserved for genuine compiler invariant violations, not ordinary
dependency absence or a cascade from a rejected provider.

## 12. Public language behavior

This redesign adds no required surface syntax. Existing source remains:

```cure
use Std.List

fn first(values: List(t)) -> Option(t) = head(values)
fn length_of(s: String) -> Int = Std.String.length(s)
```

Normative behavior:

- `head` is bare-visible because of `use Std.List`.
- `Std.String.length` is qualified-resolved without exposing bare `length`.
- `String` may be ambient because the prelude exports it.
- `Std.List`'s imports do not leak into the consumer.
- Moving either provider to a differently named file changes nothing.
- Reversing input file order changes nothing.
- Macro generation of the qualified call produces the same canonical Core as
  authored syntax.

The future `exposing` syntax changes only the lexical projection of `use`; it
does not change interface availability or build scheduling.

## 13. Required architecture changes

### 13.1 Consolidate existing foundations

Cure already has `Cure.Compiler.ModuleIndex`,
`Cure.Compiler.ModuleInterface`, `Cure.Compiler.DepGraph`, interface hashes,
incremental artifacts, and source-based environments. They SHALL become one
pipeline rather than parallel partial authorities.

- `ModuleIndex` owns module/provider identity and bootstrap edges.
- `ModuleInterface` is the only cross-module semantic export.
- the elaborator resolver owns canonical declaration resolution;
- the checked semantic graph owns invalidation and closure;
- the artifact writer owns BEAM publication; and
- the loader verifies and loads completed artifact generations only.

### 13.2 Remove transitional bridges

After consumers migrate, remove or prohibit:

- loaded-BEAM export probing for Cure name resolution;
- `env_with_generated_dependencies/2` and stamped-AST dependency scans;
- alias-dependent recovery of bare definition tails;
- compilation-entry-specific dependency sorting;
- duplicated prelude/import environment construction;
- emission-time guessing of unresolved globals; and
- source-JIT compilation that publishes an incomplete canonical generation.

### 13.3 Preserve host boundaries

Host extern validation remains explicit. Erlang/Elixir modules are not Cure
module interfaces and need not be present in the Cure source universe. Extern
owners and targets are recorded for packaging and diagnostics, while permitted
dynamic host calls remain an explicit language/FFI choice.

## 14. Implementation sequence

Each phase lands with focused regressions and a full applicable gate.

### I1 — Freeze counterexamples and invariants

- Preserve the nominal-`String`/`Regex.Syntax.Model` reversed-order fixture.
- Add authored and macro-generated qualified-call parity fixtures.
- Assert ordinary Core globals are canonical before emission.
- Trace every remaining loaded-BEAM semantic probe.

### I2 — Canonical qualified resolution

- Route qualified paths through `ModuleIndex` and `ModuleInterface` only.
- Separate interface availability from lexical `use` projections.
- Make repeated interface loads idempotent and hash-keyed.
- Remove macro-specific generated-dependency resolution.

### I3 — Prelude and semantic edge recording

- Construct the ambient prelude once from canonical interfaces.
- Record actual provider edges when ambient names are selected.
- Complete edge recording for implementations, macros, generated declarations,
  type references, externs, and runtime calls.

### I4 — Interface SCC construction

- Add skeleton predeclaration for the complete compilation universe.
- Check interface SCCs as groups.
- Implement component hashes and phase-specific cycle diagnostics.
- Ensure no partial interface enters a consumer environment.

### I5 — Body checking and validated closure

- Make definition identity canonical from predeclaration through Core,
  totality, reachability, and emission.
- Replace atom-name closure with validated `ClosureEntry` values and paths.
- Remove late bare-name recovery.

### I6 — Unified entry points and emission

- Migrate stdlib, project, incremental, test, REPL, docs, bundle, escript, and
  macro builds to the same pipeline.
- Remove semantic BEAM probing.
- Parallelize only artifact-safe work.
- Publish complete verified generations atomically.

### I7 — Cleanup and performance

- Delete superseded bridges and order-only workarounds.
- Add cold/warm interface and module timing diagnostics.
- Cache interfaces and SCCs by semantic inputs.
- Verify focused builds do not rebuild the entire stdlib unnecessarily.

## 15. Verification matrix

The work is incomplete until all of the following are automated.

### Resolution and visibility

- authored and generated qualified calls produce identical canonical Core;
- qualified access does not expose a bare name;
- `use` exposes only the direct provider's permitted surface;
- transitive dependencies leak neither bare names nor import preference;
- prelude providers are ambient without becoming direct imports;
- same-named type and constructor resolve by namespace/expected context;
- declaration and filename order do not affect canonical identity.

### Interface laws

- loading the same interface twice is idempotent;
- merge order preserves canonical identities and definitional equality;
- repeated macro expansion cannot duplicate or rekey declarations;
- source-only edits with invariant interfaces do not invalidate semantic
  consumers;
- SCC hashes are deterministic and independent of traversal order.

### Graph and cycle behavior

- every checked canonical reference has a semantic edge;
- missing dependencies fail before dependent body elaboration;
- runtime cycles compile;
- valid interface SCCs check as groups;
- invalid interface and macro cycles report full paths;
- deliberately reversed filenames and input lists produce identical artifacts.

### Emission and artifacts

- every reachable key resolves to a body or legitimate extern;
- no Cure name resolution calls the BEAM code server;
- consumers do not emit duplicate missing-module cascades after provider failure;
- clean, incremental, stdlib, project, bundle, escript, test, docs, macro, and
  REPL builds use the same module graph;
- artifact generations verify completely before publication.

### Stabilization gate

- clean dependency-independent stdlib build;
- complete `MIX_ENV=test mix test`;
- TCB and totality suites;
- relevant Antigen assays;
- no `E101` from ordinary module failures;
- no unresolved bare ordinary Core globals;
- no macro-specific module-resolution bridge;
- Unix/escript and REPL smoke tests.

## 16. Non-goals

- Replacing `use` with a new keyword.
- Making every transitive dependency authored-visible.
- Treating all cycles as legal.
- Deferring type checking until runtime.
- Adopting host BEAM modules as Cure semantic interfaces.
- Requiring a fully lazy Zig-style compiler before the interface boundary is
  corrected.
- Resuming dependent regex proofs before this pipeline and its stabilization
  gates are complete.

## 17. Acceptance criteria

This design is implemented only when:

1. the nominal-`String` reversed-order fixture builds without an ordering-only
   `use`;
2. qualified, lexical, prelude, macro, and transitive visibility laws pass;
3. all compilation entry points consume the same canonical interfaces and
   semantic graph;
4. elaboration and emission perform no loaded-BEAM semantic resolution;
5. legal runtime/interface SCCs and illegal compile-time cycles behave as
   specified;
6. incremental interface/SCC hashing is deterministic and sound;
7. provider failures yield one causal diagnostic rather than missing-module
   cascades; and
8. the full stabilization gate in section 15 is green.

