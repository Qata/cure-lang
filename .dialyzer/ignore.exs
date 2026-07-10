[
  # Dialyzer reports false positives for `if state.emit_events` guards
  # and pattern_match_cov in the Parser module.
  {"lib/cure/compiler/parser.ex", :pattern_match},
  {"lib/cure/compiler/parser.ex", :pattern_match_cov},

  # -- MapSet opaqueness false positives (Elixir 1.20-rc / OTP 29+) ----------
  #
  # `MapSet.t()` in Elixir 1.20 is deliberately NOT opaque
  # (`@type t(value) :: %__MODULE__{map: internal(value)}` where
  # `internal(value) :: %{optional(value) => term()}`), but its runtime
  # representation is built on top of `:sets.set()` which IS opaque in OTP.
  # Every call site that passes a MapSet through a public MapSet function
  # triggers `call_without_opaque` / `contract_with_opaque` because dialyzer
  # observes the declared `%MapSet{map: map()}` shape alongside the inferred
  # `%MapSet{map: :sets.set(_)}` shape and considers them incompatible. See
  # https://github.com/elixir-lang/elixir/blob/main/lib/elixir/lib/map_set.ex
  # for the rationale (struct key name kept for backwards compatibility with
  # the pre-1.15 implementation). There is nothing to fix at the call site.
  {"lib/cure/compiler/codegen.ex", :call_without_opaque},
  {"lib/cure/types/checker.ex", :call_without_opaque},
  {"lib/cure/types/effects.ex", :call_without_opaque},
  {"lib/cure/types/env.ex", :call_without_opaque},
  {"lib/cure/types/env.ex", :contract_with_opaque},
  {"lib/cure/types/pattern_checker.ex", :call_without_opaque},
  {"lib/cure/types/totality.ex", :call_without_opaque},
  {"lib/cure/repl.ex",  :call_without_opaque},

  # Same MapSet-opaqueness class on the modules added/grown since the list
  # above. `:call_with_opaque` is the sibling tag: a MapSet flowing INTO a
  # private helper as an argument (`do_closure(_, _, seen)`, `bfs_import_modules(
  # _, seen, _)`, `strictly_positive?(_, _, _, seen)`) rather than through a
  # public MapSet function. Nothing to fix at the call site — see the rationale
  # above.
  {"lib/antigen/cover_report.ex", :call_without_opaque},
  {"lib/cure/compiler/dep_graph.ex", :call_without_opaque},
  {"lib/cure/compiler/dep_graph.ex", :call_with_opaque},
  {"lib/cure/core/certificate.ex", :call_without_opaque},
  {"lib/cure/core/certificate.ex", :call_with_opaque},
  {"lib/cure/core/inductive.ex", :call_without_opaque},
  {"lib/cure/core/inductive.ex", :call_with_opaque},
  {"lib/cure/elab/implementation.ex", :call_without_opaque},
  {"lib/cure/elab/program.ex", :call_without_opaque},
  {"lib/cure/elab/program.ex", :call_with_opaque},
  {"lib/cure/elab/resolve.ex", :call_without_opaque},
  {"lib/cure/elab/resolve.ex", :call_with_opaque},
  {"lib/cure/types/env.ex", :call_with_opaque},

  # The StreamData backend is the ONE module allowed to reference StreamData,
  # a `:test`-only dep deliberately absent from dev/prod (and thus the PLT).
  # The module already carries `@compile {:no_warn_undefined, StreamData}` for
  # the compiler; this is the dialyzer counterpart of that same decision.
  {"lib/antigen/backend/stream_data.ex", :unknown_function}
]
