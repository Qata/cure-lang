# FSM Programming Guide

`fsm` is an auto-preluded standard-library macro. It expands to an ordinary
`lift module` with a checked `gen_statem` callback surface; the compiler does
not contain a separate FSM parser or object class.

## Defining An FSM

The smallest form creates a lifted module with a default state payload:

```cure
fsm Cure.TrafficLight
```

State and callback result types can be made explicit:

```cure
fsm Cure.TrafficLight state Atom handle_event
  :keep_state_and_data
```

The macro emits `callback_mode/0`, `init/1`, `handle_event/4`, and a typed
`start_link/1`. The callback result is declared as `Effect(Atom)` and erased
to the ordinary `gen_statem` return value after checking. A pure callback body
is lifted automatically; an effectful body may sequence `beam_ops`:

```cure
fsm Cure.Observed state Int handle_event
  let pid: Pid(Atom) = beam_ops self
  :keep_state_and_data
```

## Initial State And Payload

`state T` gives the module-local `State` alias used by `init/1` and the data
slot of `handle_event/4`. The explicit initializer form controls the returned
state tuple:

```cure
fsm Cure.Ready state Int init
  %[:ok, :ready, 0]
```

`with value` creates a zero-argument starter that passes the value as the
initial callback argument:

```cure
fsm Cure.Payload with 0
```

## Event Callback

The callback form receives the standard `gen_statem` arguments:

```cure
fsm Cure.Counter state Int handle_event
  match event
    :increment -> :keep_state_and_data
    _ -> :keep_state_and_data
```

The `event_type`, `event`, `state`, and `data` names are available in the
callback body. The body must elaborate to the declared `Effect(Atom)` result.
Nested macros are expanded before the callback is checked.

## Runtime

The generated module is an ordinary BEAM module and can be started through its
checked helper:

```cure
mod Cure.Driver
  use Std.Fsm

  fn start() -> Effect(Tuple) =
    beam_ops start_statem :"Cure.TrafficLight" [0]
```

For runtime registry and inspection helpers, use `Std.Fsm`:

```cure
let pid = Std.Fsm.spawn(:"Cure.TrafficLight")
Std.Fsm.send(pid, :tick)
let alive = Std.Fsm.is_alive(pid)
Std.Fsm.stop(pid)
```

## Transparency

The expansion is ordinary Cure syntax. It contains no `__otp_container`
marker, raw-source compilation, or direct code-server load. Generated modules
are collected and emitted by the same generic lifted-module path as any
user-defined macro.

Transition-table and richer event/state derivation remain language-level
macro work built on this callback floor; they are not compiler-owned syntax.
