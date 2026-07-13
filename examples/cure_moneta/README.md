# cure_moneta

A money and ledger library written in Cure. The example focuses on ADTs,
records, dependent data, and checked foreign calls. Its process
surface uses the transparent standard-library macros rather than a bespoke
FSM compiler.

## Quick start

```bash
cd examples/cure_moneta
mix deps.get
mix test
```

## Domain model

```cure
type Currency = EUR | USD | GBP | JPY | CHF | OMR

rec Money
  amount: Int
  currency: Currency
  fractional_units: Int

rec Ledger
  accounts: List(Account)
```

The ledger operations are pure and return `Result` values. Currency rendering,
functional record updates, and the float FFI are all ordinary Cure declarations.

## Transparent process floor

`cure_src/transaction.cure` declares a transparent FSM module:

```cure
fsm Cure.Transaction with 0
  fn initial_state() -> Atom = :idle
```

The `fsm` macro expands to a lifted module and uses `Std.Otp.start_statem` for
startup. A transition-aware version can be expressed entirely in Cure:

```cure
fsm Cure.TransactionFlow state Int transitions [
  transition :idle :create :pending,
  transition :pending :submit :settled
]
```

The transition rows are checked ADT values and dispatch is a normal recursive
Cure function. No `on_transition` parser or compiler-owned FSM class is involved;
the generated `Cure.Transaction` module is a transparent lifted module.
class is involved.

## Layout

```text
cure_src/moneta.cure       domain types and ledger operations
cure_src/transaction.cure  transparent FSM floor
lib/cure_moneta.ex         Elixir-facing facade
test/cure_moneta_test.exs  domain and interop tests
```
