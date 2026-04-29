# Toolchain Requirements

## Lean 4

- Toolchain: `leanprover/lean4:v4.30.0-rc2`
  - Pinned by `ZkKzgAuth/lean-toolchain`. `elan` reads this file automatically and installs the matching version on first build.
- Mathlib: pulled by `lake build` at the commit recorded in `ZkKzgAuth/lake-manifest.json`. Do not regenerate the manifest manually; doing so may break the proofs against newer Mathlib API.

### Install

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Then:

```sh
cd ZkKzgAuth
lake build
```

The first build downloads Mathlib (~1 GB of source plus a `.lake/` cache) and may take several minutes. Subsequent builds are incremental.

## Rust

- Edition: 2021
- Toolchain: stable Rust, tested on 1.90.0 (2025-09-14)
- Dependencies (pinned in `zk_kzg_sim/Cargo.toml` and locked in `Cargo.lock`):
  - `ark-bn254` 0.4.0
  - `ark-ec` 0.4.0
  - `ark-ff` 0.4.0
  - `ark-poly` 0.4.2
  - `ark-std` 0.4.0
  - `rand` 0.8.5

### Install

```sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Then:

```sh
cd zk_kzg_sim
cargo build --release
cargo run --release
```

The release-profile build is required; the debug profile is roughly 50× slower for elliptic-curve operations and the reported latencies will not reproduce.
