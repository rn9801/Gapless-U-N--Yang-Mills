# Gaplessness of four-dimensional Wilson U(N) at weak coupling

[Read the paper](U-N-4D-mass-gap-proof.pdf).

This repository contains a partial Lean 4 formalization of the fixed-lattice-spacing argument.
The main spectral claim for the infinite-volume Wilson measure, Theorem 1, remains unproved in Lean.

## Build and check

Use the Lean version pinned in `lean-toolchain`. Mathlib is the project's only direct dependency.

```bash
lake build
lake env lean -DwarningAsError=true CheckProofs.lean
```

The first build can use the official Mathlib cache with `lake exe cache get` where it is reachable.
The proof audit checks the project declarations and their transitive axiom dependencies. It permits
Lean's standard foundations `propext`, `Classical.choice`, and `Quot.sound`.

## Correspondence with the paper

| Paper | Lean development |
| --- | --- |
| §1, exterior derivative | [Lattice.lean](GaplessYangMills/Lattice.lean) defines positive cells and proves d² = 0. |
| §§2–3, rare defects | [WeakCoupling.lean](GaplessYangMills/WeakCoupling.lean) checks the numerical cap bound and ρ < 1 for β ≥ 10⁴. [MarkedEdges.lean](GaplessYangMills/MarkedEdges.lean) derives (1) from the joint bad-face estimate. The Wilson-law proof of that joint estimate remains open here. |
| §3, lifted flux and fills | [Flux.lean](GaplessYangMills/Flux.lean) proves integrality and closedness of the defect under the determinant cube identity. [Wilson.lean](GaplessYangMills/Wilson.lean) proves the determinant cube identity for unitary links. [FiniteFilling.lean](GaplessYangMills/FiniteFilling.lean) fills finitely supported integer edge cycles. The good-cube vanishing proof, quantitative filling bounds and infinite-volume approximation (4) remain open here. |
| §4, central response | The unitary link rotation, exact lift and cut-shift identity, finite log-weight derivative, and closed-form zero-sum lemma are checked in [Wilson.lean](GaplessYangMills/Wilson.lean), [Flux.lean](GaplessYangMills/Flux.lean), [Action.lean](GaplessYangMills/Action.lean), and [Ward.lean](GaplessYangMills/Ward.lean). Deriving the response kernel and its integrability for a Wilson Gibbs state remains open here. |
| §5, spectral obstruction | [DirectionalMean.lean](GaplessYangMills/DirectionalMean.lean) preserves the Ward identities when subtracting an existing directional Cesàro mean. [Spectral.lean](GaplessYangMills/Spectral.lean) gives the gapped spectral remainder after removing the entire vacuum projection. [Decay.lean](GaplessYangMills/Decay.lean) proves that exponential decay implies summability. The reflection-positive Hilbert-space construction and identification of the local matrix elements for the Wilson state remain open here. |

The theorem `not_summable_of_ward` expresses the contradiction in §5 by summing over
transverse lattice slices. The theorem `spectrum_near_one_of_ward` combines this
contradiction with the decay estimates to get spectral points arbitrarily close to 1.
Its hypotheses include the Ward identities and quantitative bounds for local approximants
of the correlation kernel after subtracting directional means.
