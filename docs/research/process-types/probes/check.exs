# Elaborate a single .cure probe file and report ACCEPT / REJECT.
# Usage: mix run --no-start docs/research/process-types/probes/check.exs <file.cure>
alias Cure.Elab.Program

[path] = System.argv()
src = File.read!(path)

case Program.elaborate(src) do
  {:ok, _env} ->
    IO.puts("ACCEPT  #{path}")

  {:error, reason} ->
    IO.puts("REJECT  #{path}")
    IO.puts("  " <> inspect(reason, pretty: true, limit: 8))
    System.halt(1)
end
