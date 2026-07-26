# CureTurnstile

A small Cure process example using the transparent FSM macro.

The source in `cure_src/turnstile.cure` is intentionally small:

```cure
fsm Cure.Turnstile with 0
  fn initial_state() -> Atom = :locked
```

`fsm` is an auto-preluded standard-library macro. It expands to an ordinary
lifted module and uses the checked `Std.Otp` process algebra for startup. There
is no FSM-specific compiler object or source-string callback parser.

Transition tables can be defined in Cure data and dispatched by ordinary
standard-library code:

```cure
fsm Cure.Light state Int transitions [
  transition :locked :coin :unlocked,
  transition :unlocked :push :locked
]
```

The generated module is named exactly as declared, `Cure.Turnstile`, and its
callbacks are emitted by the common lifted-module writer.

## Usage

```bash
cd examples/cure_turnstile
mix deps.get
mix compile
mix test
```

The Elixir wrapper in `lib/` remains ordinary application code. It is useful
for demonstrating interop, but it does not implement the Cure FSM semantics.
