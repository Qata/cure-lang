# Ensure the Cure standard library is compiled to BEAM before the suite
# runs.
#
# Several test files (notably `test/cure/stdlib/iter_test.exs`,
# `test/cure/stdlib/pbt_test.exs`, and anything else that relies on
# `Cure.Stdlib.Preload.preload/1`) expect
# `_build/cure/ebin/Cure.Std.*.beam` to exist at startup. Locally we
# usually have the beams lying around from a previous `mix cure.compile_stdlib`
# invocation, so everything works. In CI (and on any truly fresh
# checkout) there is no `_build/cure/ebin` yet, so the preload helper
# silently does nothing and the tests above fail with
# `UndefinedFunctionError: function :"Cure.Std.Iter".from_list/1 is undefined`.
#
# Running the compile task here pays the cost once per suite, guarantees
# the beams are present, and keeps the dependency explicit.
#
# We compile UNCONDITIONALLY rather than gating on the presence of a single
# sentinel beam. A presence check cannot notice that a stdlib source changed
# since its beam was built, so an edited module (e.g. `lib/std/vector.cure`)
# would leave a stale `_build/cure/ebin/*.beam` in place and produce ordering-
# dependent test flakes. A full recompile once per suite is a few seconds and
# is always correct.
IO.puts("test_helper: compiling Cure stdlib")
Mix.Task.run("cure.compile_stdlib")

ExUnit.start()
