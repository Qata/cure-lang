# OTP metatheory

This directory contains the research corpus for Cure's OTP formalisation. It is
deliberately separate from the shipped standard library:

- `src/` contains executable models, relations, and machine-checked proofs.
- `test/` contains the corresponding ExUnit regression corpus.
- `oracle/otp/` remains the paired Cure/Idris verdict corpus.

The reusable process algebra is the standalone `cure-otp` package beside the
`cure-lang` repository. Its three source modules (`Otp.Raw`, `Otp.Beam`, and
`Otp`) do not import this metatheory corpus. The `Std.Otp` modules remain the
stdlib compatibility surface for existing Cure programs.

Run the isolated corpus explicitly:

```sh
mix cure.compile metatheory/otp/src --output-dir _build/metatheory/otp/ebin
mix test metatheory/otp/test
```

Ordinary stdlib compilation and `mix test` do not discover this directory.
