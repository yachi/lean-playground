# LeanPlayground

A private playground for doing mathematics in Lean 4 with Mathlib.

## Setup

The toolchain comes from [mise](https://mise.jdx.dev) and [elan](https://github.com/leanprover/elan).
`mise.toml` pins elan and puts `~/.elan/bin` on `PATH` inside this directory.
`lean-toolchain` pins the Lean version, and elan installs it on first use.

```fish
mise install
elan-init -y --default-toolchain none --no-modify-path  # once per machine
lake exe cache get   # download prebuilt Mathlib (~9k files); never build Mathlib from source
lake build
```

## Layout

- `LeanPlayground/` — playground files. Each file starts with `module` and `public import Mathlib`.
- `LeanPlayground.lean` — the library root. Import every new file here so `lake build` checks it.

## Update Mathlib

```fish
lake update
```

The `update.yml` workflow also opens a pull request when a new Mathlib release is out.
