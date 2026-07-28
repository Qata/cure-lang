%{
  title: "Playground",
  description: "Status of the browser playground during the dependent-compiler transition.",
  order: 13
}
---

## Current status

The pre-0.34 Playground is not a supported compiler surface. Its LiveView still
references the deleted `Cure.Types.Checker` and classic code generator, so it
must not be presented as performing authoritative checking or safe evaluation.

The supported interactive surfaces are:

- `cure repl` for checked local exploration;
- `cure check <file>` for dependent elaboration without emission;
- `cure run <file>` for checked compilation and `main/0` execution;
- editor/LSP integrations for structured diagnostics and holes.

## Required dependent port

A restored browser Playground must use the same headless dependent front end,
canonical module loader, stdlib/prelude discovery, structured diagnostics, and
validated emission path as the CLI. It must not call a compatibility checker or
bypass Core validation. Evaluation must retain process isolation, output
capture, memory limits, and a hard execution deadline.

Until that port lands, `/playground` should be treated as unavailable rather
than as a weaker classic-only compiler.

## Historical implementation

The v0.27/v0.28 site provided a debounced editor, Makeup highlighting, a
classic-checker panel, and a sandboxed BEAM evaluator. Those UI ideas remain
useful, but the checker and emitter integration described in the old page was
removed with the classic pipeline.

## Related

- [REPL](/repl)
- [Tooling](/tooling)
- [Type System](/type-system)
- [Roadmap](/roadmap)
