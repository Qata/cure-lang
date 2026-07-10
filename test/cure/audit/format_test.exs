defmodule Cure.Audit.FormatTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Format
  alias Cure.Audit.Ledger.{Axiom, Report}

  defp report do
    %Report{
      axioms: [
        %Axiom{
          mfa: {:erlang, :length, 1},
          type: "∀ {a}. List(a) -> Int",
          via: :length,
          bucket: :otp
        }
      ],
      builtin_count: 31,
      not_proven_total: [:reverse, :last, :drop, :take]
    }
  end

  test "renders every section, including empty ones" do
    text = Format.to_text(report(), [])

    assert text =~ "AXIOMS — OTP (1)"
    assert text =~ "erlang:length/1"
    assert text =~ "∀ {a}. List(a) -> Int"
    assert text =~ "AXIOMS — CURE RUNTIME (0)"
    assert text =~ "AXIOMS — CURE BRIDGE (0)"
    assert text =~ "OPAQUE TYPES (0)"
    assert text =~ "31 builtin operators"
    assert text =~ "HOLES (0)"
    assert text =~ "ABSURD (0)"
    assert text =~ "NOT PROVEN TOTAL (4)"
    assert text =~ "cannot be used in proofs; not assumptions"
    assert text =~ "UNAUDITED (0)"
  end

  test "omits the target section unless --target was given" do
    refute Format.to_text(report(), []) =~ "UNAVAILABLE ON TARGET"
    assert Format.to_text(report(), target: :atomvm) =~ "UNAVAILABLE ON TARGET (0)"
  end

  test "reports an unavailable axiom for the named target" do
    r = %Report{
      axioms: [%Axiom{mfa: {:re, :run, 3}, type: "Binary -> Binary", via: :run, bucket: :otp}]
    }

    text = Format.to_text(r, target: :atomvm)
    assert text =~ "UNAVAILABLE ON TARGET (1)"
    assert text =~ "re:run/3"
    assert text =~ ":re absent on atomvm"
  end

  test "output is byte-identical across runs" do
    assert Format.to_text(report(), []) == Format.to_text(report(), [])
    assert Format.to_json(report(), []) == Format.to_json(report(), [])
  end

  test "json carries a schema version and the same axiom set" do
    # `Jason` is NOT a dependency of this project. Do not add one. Assert on the
    # emitted string.
    json = Format.to_json(report(), [])
    assert json =~ ~s("schema":1)
    assert json =~ ~s("mfa":"erlang:length/1")
    assert json =~ ~s("bucket":"otp")
    assert json =~ ~s("builtin_count":31)
    assert String.ends_with?(json, "}\n")
  end

  test "json escapes every string field, not just type and holes" do
    # A target module/function atom can contain a quote or backslash. If any
    # interpolated field is emitted raw, the whole JSON document is corrupt.
    r = %Report{
      axioms: [
        %Axiom{
          mfa: {:"evil\"mod", :"f\\n", 1},
          type: "Int",
          via: :"weird\"name",
          bucket: :otp
        }
      ],
      opaque: [:"O\"pq"],
      not_proven_total: [:"n\\t"],
      unresolved: [:"u\"r"]
    }

    json = Format.to_json(r, [])
    # No unescaped double-quote may appear inside a string value. A cheap proxy:
    # the raw atom text must not survive verbatim.
    refute json =~ ~s(evil"mod)
    refute json =~ ~s(weird"name)
    refute json =~ ~s(O"pq)
    assert json =~ ~S(evil\"mod)
    assert json =~ ~S(weird\"name)
  end

  test "json escapes control characters, which JSON forbids raw" do
    # A raw newline/tab inside a JSON string is illegal (RFC 8259 §7). They must
    # be emitted as \n / \t escape sequences.
    r = %Report{
      axioms: [%Axiom{mfa: {:m, :f, 1}, type: "a\nb\tc", via: :v, bucket: :otp}]
    }

    json = Format.to_json(r, [])
    refute json =~ "a\nb", "raw newline leaked into JSON"
    assert json =~ ~S(a\nb\tc)
  end

  test "render/2 selects the format" do
    assert Format.render(report(), format: "json") =~ ~s("schema":1)
    assert Format.render(report(), format: "text") =~ "AXIOMS — OTP (1)"
    assert Format.render(report(), []) =~ "AXIOMS — OTP (1)"
  end
end
