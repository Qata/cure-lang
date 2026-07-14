# Applications And Releases

`app` is an auto-preluded standard-library macro that creates a transparent
lifted `Application` module. Project metadata remains in `Cure.toml`; startup,
shutdown, and phase callbacks are ordinary checked Cure declarations.

## Basic Application

A phase-only application can be declared directly:

```cure
app Cure.Demo
```

The generated module has checked `start/2` and `stop/1` callbacks. Callback
results use erased `Effect(...)` types, so pure results and effectful bodies
share one elaboration path.

## Root Supervisor

Use the root form to start a supervisor through the checked BEAM algebra:

```cure
app Cure.Demo root :"Cure.Root"
```

An initial payload can be supplied:

```cure
app Cure.Demo root :"Cure.Root" with 0
```

The generated `start/2` calls `beam_ops start_supervisor` and preserves the
ordinary OTP startup tuple after effect erasure. Root values are code, so a
qualified module atom or another transparent expression can be supplied.

## One Or More Phases

A single delayed phase body can sequence operations:

```cure
app Cure.Phased phase :warm_cache
  let pid: Pid(Atom) = beam_ops self
  :ok
```

Multiple pure phase results use the transparent `phases` form. Entries are a
flat list of alternating phase and result atoms:

```cure
app Cure.MultiPhase phases [:warm_cache, :warmed, :ready, :started]
```

Unknown phases return `:ok`, matching the ordinary application callback
convention. Richer effectful phase bodies use the single `phase` form and can
be composed by a user-defined macro over the same checked primitives.

## Project Metadata

The application manifest is declared separately:

```toml
[project]
name = "demo"
version = "0.1.0"

[application]
name = "demo"
vsn = "0.1.0"
applications = ["logger", "crypto"]
start_phases = ["warm_cache", "ready"]

[application.env]
port = 4000

[release]
name = "demo"
vsn = "0.1.0"
include_erts = false
```

`Cure.Project.compile_project/2` discovers the lifted application module,
enforces the single-application invariant, checks its name against
`[application].name`, and emits the `<name>.app` resource. Release generation
uses the same compiled modules and manifest data.

## Runtime API

Use `Std.App` for application management and environment access:

```cure
mod Cure.Control
  use Std.App

  fn boot() -> Atom = Std.App.ensure_all_started(:demo)
  fn port() -> Int = Std.App.get_env_or(:demo, :port, 4000)
```

## Transparency

The `app` macro expands to ordinary `lift module`, `callback`, and checked
algebra syntax. It does not use an OTP-specific compiler branch, source-string
compilation, or direct code-server loading.
