# Cure Lean Bridge

Stage-1 CLI bridge for Lean-hosted dependent checking.

The Elixir side runs one process per request and sends a single JSON object in
`CURE_LEAN_BRIDGE_REQUEST`. The bridge also accepts stdin for manual use. It
writes one JSON response on stdout.

## Build

```sh
lake build
```

The Lake package expects a local `lean4lean` checkout at `../../lean4lean` from
this directory. Override the runtime health-check path with
`CURE_LEAN4LEAN_PATH`; if the checkout is somewhere else, update the Lake
dependency path or build from a matching checkout layout.

## Protocol

Health request:

```json
{"op":"health","protocol":1}
```

Successful response:

```json
{"status":"ok","protocol":1,"lean_version":"...","lean4lean_path":"...","lean4lean_available":true}
```

`check_module` is reserved for the Cure-to-Lean translation stage and currently
returns a structured `translation_unimplemented` diagnostic.

## Admitted Core Fragment

The Elixir encoder only sends the Lean-shaped fragment currently checked by the
bridge:

- `type`
- `var`
- `pi`
- `lam`
- `app`
- `global` names that can be safely namespaced as Lean constants
- `eq` translated to Lean `Eq`
- `refl` translated to Lean `Eq.refl`
- `rewrite` translated to Lean `Eq.ndrec`

Everything else is rejected before the bridge until it has a principled Lean
translation. In particular, the encoder blocks Cure convenience nodes such as
`absurd`, primitive operations and literals, raw constructor/data nodes, `case`,
holes, and unsafe bare atom names.
