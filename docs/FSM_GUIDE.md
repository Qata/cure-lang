# FSM Programming Guide

`fsm` is an auto-preluded standard-library macro. It expands to an ordinary
`lift module` with a checked `gen_statem` callback surface; the compiler does
not contain a separate FSM parser or object class.

## Defining An FSM

The preferred surface is the transition graph itself:

```cure
fsm Cure.Turnstile with Int
  Locked --Coin--> Unlocked
    update data + 1
  Unlocked --Push--> Locked
  Unlocked --Coin--> Unlocked
    update data + 1
  Locked --Push--> Locked
```

`with Int` declares the machine's data type. The macro catalogs every endpoint
into a nominal `State` type (`Locked | Unlocked`) and every label into a nominal
`Event` type (`Coin | Push`). The first source state is the initial state.

An edge preserves `data` unless it has an indented `update` expression. The
expression is checked as the declared data type and may refer to `data`; the
target state is already fixed by the edge and is not repeated in callback
tuples.

## Transition Tables

Transition rows are parsed by a grammar production declared in `Std.Fsm`, not
by a compiler-owned FSM parser:

```cure
fsm Cure.Light with Int
  Red --Timer--> Green
  Green --Timer--> Yellow
  Yellow --Timer--> Red
```

The generated callback is direct nested pattern matching over the derived
constructors. It returns checked `FsmAction` values and lowers them to the
native `gen_statem` protocol; no transition table or syntax interpreter remains
at runtime.

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

The transition grammar and event/state derivation are language-level macro
work. Another package can define the same kind of declarative algebra without
changing the compiler.
