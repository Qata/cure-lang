# Typed Supervision Trees

`actor` and `sup` are auto-preluded standard-library macros. Each expands to
an ordinary lifted module and is checked and emitted through the common Cure
pipeline. OTP behavior knowledge belongs in these Cure definitions and the
checked `Std.Otp` algebra, not in a bespoke compiler object class.

## Actors

An actor creates a lifted `gen_server` module. The explicit state form shares a
`State` alias across all state-bearing callbacks:

```cure
actor Cure.Counter state Int handle_info
  let pid: Pid(Atom) = beam_ops self
  %[:noreply, state + 1]
```

Other callback forms include `init` and typed synchronous calls:

```cure
actor Cure.Calculator state Int call Int returns Bool
  %[:reply, true, state]
```

Callback results are checked as erased `Effect(...)` values. Pure values are
lifted automatically, while `beam_ops` expressions must satisfy the ordinary
process algebra. The generated module exports the normal `gen_server`
callbacks and a checked `start_link` helper.

## Supervisors

The smallest supervisor is transparent and runnable:

```cure
sup Cure.Root
```

Child declarations use the closed `Std.Supervisor` vocabulary:

```cure
sup Cure.Root children [Std.Supervisor.child(:"Cure.Counter", :counter)]
```

Child policies are typed values rather than arbitrary atoms:

```cure
mod Cure.Specs
  use Std.Supervisor

  fn child_spec() -> ChildSpec =
    Std.Supervisor.child_with_args(
      :"Cure.Counter",
      :counter,
      [0],
      Std.Supervisor.permanent(),
      Std.Supervisor.shutdown_after(5000),
      Std.Supervisor.worker()
    )
```

`Restart`, `Shutdown`, and `ChildType` are closed Cure values. Intensity and
period use `Nat`, so negative literals and unrestricted `Int` values are
rejected by ordinary elaboration. The generated `init/1` callback returns the
standard supervisor strategy and child-spec structure.

## The BEAM Algebra

Process operations are expressed with `beam_ops` and checked `Std.Otp`
functions:

```cure
mod Cure.ProcessUser
  use Std.Otp

  fn me() -> Effect(Pid(Atom)) = beam_ops self
  fn tell(pid: Pid(Atom)) -> Effect(Unit) = beam_ops tell pid :ping
```

The message and reply indices are static only and erase to ordinary BEAM pids
and terms. The raw extern boundary is isolated in `Std.Otp.Raw`.

## Runtime Helpers

`Std.Supervisor` exposes runtime registry helpers for already-emitted modules:

```cure
let pid = Std.Supervisor.start(:"Cure.Root")
let children = Std.Supervisor.which_children(:"Cure.Root")
Std.Supervisor.stop(:"Cure.Root")
```

The direct `:supervisor` startup used by generated `app` modules goes through
`beam_ops start_supervisor`, so it has the same checked effect path.

## Transparency

The macro expansion contains no `__otp_container`, raw-source compilation, or
direct code-server load. Nested macros and callback bodies are recursively
parsed and elaborated before the generic lifted-module emitter writes BEAM
forms. New user-defined actor-like abstractions can use the same `lift module`,
`callback`, and algebra vocabulary without compiler changes.
