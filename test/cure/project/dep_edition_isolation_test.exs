# Iteration 6 (LATENT-1 residual): a path/tarball dependency compiles under its
# OWN edition (its manifest, or the compiler default), NEVER the consuming
# project's — Rust's edition-per-package rule. Before this fix the dep-compile
# sites in Cure.Project passed no :project_dir, so Cure.Compiler.resolve_edition
# fell back to find_root/1, which walks UP from the dep's own source file. A dep
# that ships without its own Cure.toml (and without a `.git` boundary under
# _build/deps) therefore discovered the CONSUMER's manifest and inherited its
# edition. When that consumer edition is a typo (unknown), the dep compile failed
# silently (errors are swallowed by `_ =`) and its .beam was never produced.
defmodule Cure.Project.DepEditionIsolationTest do
  use ExUnit.Case, async: true

  setup do
    root = Path.join(System.tmp_dir!(), "cure_depiso_#{System.unique_integer([:positive])}")
    File.mkdir_p!(root)
    on_exit(fn -> File.rm_rf!(root) end)
    {:ok, root: root}
  end

  test "a manifest-less path dep compiles under the default edition, not the consumer's typo'd one",
       %{root: root} do
    # Consumer manifest declares an UNKNOWN edition. If the dep inherits it, the
    # dep compile fails and no .beam is emitted.
    File.write!(Path.join(root, "Cure.toml"), "[project]\nname = \"app\"\nedition = \"9999\"\n")

    # Path dep lives INSIDE the consumer tree, ships lib/*.cure but NO Cure.toml.
    dep_lib = Path.join([root, "dep", "lib"])
    File.mkdir_p!(dep_lib)
    File.write!(Path.join(dep_lib, "d.cure"), "mod DepMod\n  fn f() -> Int = 1\n")

    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{path: "dep", name: "mydep"}]
    }

    assert :ok = Cure.Project.resolve_deps(project)

    dep_ebin = Path.join(root, "_build/deps/mydep")
    beams = Path.wildcard(Path.join(dep_ebin, "*.beam"))

    assert beams != [],
           "expected the path dep to compile under the default edition and emit a .beam, " <>
             "but none was produced — it inherited the consumer's unknown edition"
  end

  # Iteration 6 (audit A1-F2): a dependency whose inline table has a present-but-
  # BLANK path (`foo = { path = "" }`) previously routed to the git-clone clause
  # (parse_dep_line always emits a `git: nil` key), building `git clone … nil …`
  # and CRASHING System.cmd with an ArgumentError. A malformed dep must fail with
  # a clean error tuple, not raise.
  test "a dependency with a blank path fails with an error, not a crash", %{root: root} do
    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{name: "bad", path: "", git: nil, tag: nil, version: nil, constraint: nil}]
    }

    assert {:error, {:invalid_dependency, "bad"}} = Cure.Project.resolve_deps(project)
  end

  # Iteration 7 (audit A1-F3): the blank-path rejection must also catch a
  # WHITESPACE-only path. `path = "   "` satisfies the `!= ""` guard literally, so
  # it slipped into the path clause, expanded to `<root>/   `, found zero files,
  # and silently "resolved" to :ok — defeating the malformed-dep rejection.
  test "a whitespace-only path is rejected, not silently resolved", %{root: root} do
    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{name: "bad", path: "   ", git: nil, tag: nil, version: nil, constraint: nil}]
    }

    assert {:error, {:invalid_dependency, "bad"}} = Cure.Project.resolve_deps(project)
  end

  # Iteration 7 (audit A3-F1): a dependency whose OWN Cure.toml declares an unknown
  # edition must FAIL LOUDLY, not silently. dep_project_dir now routes the dep's
  # manifest into resolve_edition, so a typo'd dep edition makes compile_file return
  # {:edition_error, …}. That error was discarded (`_ =`), leaving the build green
  # with no beams and only opaque missing-module errors downstream. Propagate it.
  test "a dependency's own unknown edition fails the build loudly", %{root: root} do
    dep = Path.join(root, "dep")
    dep_lib = Path.join(dep, "lib")
    File.mkdir_p!(dep_lib)
    # The DEP ships its own manifest with a typo'd edition.
    File.write!(Path.join(dep, "Cure.toml"), "[project]\nname = \"dep\"\nedition = \"9999\"\n")
    File.write!(Path.join(dep_lib, "d.cure"), "mod DepMod\n  fn f() -> Int = 1\n")

    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{name: "mydep", path: "dep", git: nil, tag: nil, version: nil, constraint: nil}]
    }

    assert {:error, {:dependency_edition_error, "mydep", {:unknown_edition, "9999"}}} =
             Cure.Project.resolve_deps(project)
  end
end
