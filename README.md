# ZK-KZG-Auth

Reference implementation and Lean 4 formal verification artifacts for the protocol described in the ICMIC 2026 paper *"Machine-Checked Privacy: A Formally Verified Zero-Knowledge Authentication Protocol for 6G Cell-Free Massive MIMO."*

This repository is published as a peer-review artifact. It contains exactly the source needed to inspect and reproduce the formal proofs and the latency measurements reported in the paper.

## Layout

| Path | Contents |
|---|---|
| `ZkKzgAuth/` | Lean 4 development. Defines the protocol's blinded KZG transcript and proves Completeness, the algebraic basis of Knowledge Soundness, and Zero-Knowledge against an abstract bilinear-pairing model. Compiles with `lake build`. No `sorry` placeholders. |
| `zk_kzg_sim/` | Rust reference implementation using the arkworks BN254 backend. Used for the latency measurements reported in Section VI of the paper. Sample output is included in `benchmark_results.txt` and `benchmark_x86.csv`. |
| `requirements/` | Toolchain version pins for Lean and Rust. |

## Quickstart

### Lean development

```sh
cd ZkKzgAuth
lake build
```

The toolchain is pinned by `ZkKzgAuth/lean-toolchain`; `elan` will install the matching Lean version automatically. The first `lake build` will fetch Mathlib at the commit recorded in `ZkKzgAuth/lake-manifest.json`.

### Rust benchmark

```sh
cd zk_kzg_sim
cargo run --release
```

Outputs latency tables to stdout and writes a CSV to `benchmark_x86.csv` (or the platform-appropriate name).

## License

MIT. See `LICENSE`.
