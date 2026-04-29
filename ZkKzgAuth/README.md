# ZkKzgAuth (Lean 4 development)

Formal verification of the ZK-KZG-Auth protocol, written against an abstract bilinear-pairing model.

The full development is a single file: `ZkKzgAuth/Basic.lean`. It contains:

- `Bilinear` structure capturing the three pairing axioms (additive distributivity in each argument, scalar-shift law).
- Definitions of the protocol's transcript components: `proofPi`, `proofV`, `commitC`, and `simulator`.
- Three theorems:
  - `zk_kzg_completeness` — honest UE always authenticates.
  - `zk_kzg_extractor_consistency` and `zk_kzg_soundness_dichotomy` — algebraic basis of Knowledge Soundness via two-transcript extraction.
  - `simulator_passes_verification` and `zk_kzg_zero_knowledge` — perfect Zero-Knowledge: the simulator's output, computed without `P(X)`, is identically distributed to honest transcripts.

`lake build` compiles the whole development. There are no `sorry` placeholders. The only admitted axioms are the three `Bilinear` properties enumerated in the paper's Section V.A.

See the project root `requirements/` for toolchain installation.
