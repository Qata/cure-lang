defmodule Cure.Compiler.AtomVMContainerTest do
  use ExUnit.Case, async: false

  @moduletag :atomvm

  test "all transparent OTP macros run on generic-unix AtomVM" do
    atomvm_root = System.get_env("ATOMVM_ROOT", "/Users/ch/Develop/esp32-beam/AtomVM")
    atomvm = Path.join(atomvm_root, "build/src/AtomVM")
    packbeam = Path.join(atomvm_root, "build/tools/packbeam/packbeam")
    estdlib = Path.join(atomvm_root, "build/libs/estdlib/src/beams")

    if File.exists?(atomvm) and File.exists?(packbeam) and File.dir?(estdlib) do
      out = Path.join(System.tmp_dir!(), "cure_atomvm_test_#{System.unique_integer([:positive])}")
      File.mkdir_p!(out)

      on_exit(fn -> File.rm_rf!(out) end)

      assert {:ok, :"Cure.AtomVMTestSup", _} =
               Cure.Compiler.compile_string("sup Cure.AtomVMTestSup\n",
                 output_dir: out,
                 emit_events: false
               )

      assert {:ok, :"Cure.AtomVMTestApp", _} =
               Cure.Compiler.compile_string("app Cure.AtomVMTestApp\n",
                 output_dir: out,
                 emit_events: false
               )

      assert {:ok, :"Cure.AtomVMTestActor", _} =
               Cure.Compiler.compile_string("actor Cure.AtomVMTestActor with 0\n",
                 output_dir: out,
                 emit_events: false
               )

      assert {:ok, :"Cure.AtomVMTestFsm", _} =
               Cure.Compiler.compile_string("fsm Cure.AtomVMTestFsm with 0\n",
                 output_dir: out,
                 emit_events: false
               )

      forms = [
        {:attribute, 1, :module, :cure_atomvm_probe},
        {:attribute, 1, :export, [{:start, 0}]},
        {:function, 1, :start, 0,
         [
           {:clause, 1, [], [],
            [
              remote_call(:"Cure.AtomVMTestSup", :start_link, []),
              remote_call(:"Cure.AtomVMTestApp", :start, [{:atom, 1, :normal}, {nil, 1}]),
              remote_call(:"Cure.AtomVMTestActor", :start_link, []),
              remote_call(:"Cure.AtomVMTestFsm", :start_link, []),
              remote_call(:io, :format, [{:string, 1, ~c"CURE_ATOMVM_PROOF_OK~n"}, {nil, 1}])
            ]}
         ]}
      ]

      assert {:ok, :cure_atomvm_probe, binary, _warnings} = Cure.Compiler.BeamWriter.compile_forms(forms)
      probe = Path.join(out, "cure_atomvm_probe.beam")
      File.write!(probe, binary)

      beams = [probe | Path.wildcard(Path.join(estdlib, "*.beam"))]
      beams = beams ++ Path.wildcard(Path.join(File.cwd!(), "_build/cure/ebin/Cure.Std.*.beam"))

      beams =
        [
          Path.join(out, "Cure.AtomVMTestSup.beam"),
          Path.join(out, "Cure.AtomVMTestApp.beam"),
          Path.join(out, "Cure.AtomVMTestActor.beam"),
          Path.join(out, "Cure.AtomVMTestFsm.beam")
          | beams
        ]

      archive = Path.join(out, "cure_atomvm_proof.avm")

      {_output, 0} =
        System.cmd(packbeam, ["create", "--start", "cure_atomvm_probe", archive | beams], cd: atomvm_root)

      {output, 0} = System.cmd(atomvm, [archive], cd: atomvm_root)
      assert output =~ "CURE_ATOMVM_PROOF_OK"
    else
      assert true
    end
  end

  defp remote_call(module, function, args) do
    {:call, 1, {:remote, 1, {:atom, 1, module}, {:atom, 1, function}}, args}
  end
end
