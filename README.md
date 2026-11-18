# Gaplessness of four-dimensional Wilson U(N) at weak coupling

[Read the paper](U-N-4D-mass-gap-proof.pdf).

This repository contains a partial Lean 4 formalization of the argument at fixed lattice spacing.
Theorem 1 for the infinite-volume Wilson transfer operator remains open in this development.

## Build and check

Use the Lean version pinned in `lean-toolchain`. Mathlib is the project's only direct dependency.

```bash
lake build
lake env lean -DwarningAsError=true CheckProofs.lean
```

The first build can use the official Mathlib cache with `lake exe cache get` where it is reachable.
The audit checks project declarations, including private ones, and their transitive axiom dependencies.
It permits Lean's standard foundations `propext`, `Classical.choice`, and `Quot.sound`.

## Correspondence with the paper

| Paper | Checked in Lean |
| --- | --- |
| §1 | Cubical exterior derivatives, the periodic Wilson probability measure, the finite-volume conditional Gibbs law, existence of weak subsequential limits, and translation invariance. [Lattice](GaplessYangMills/Lattice.lean), [FiniteWilson](GaplessYangMills/FiniteWilson.lean), [FiniteGibbs](GaplessYangMills/FiniteGibbs.lean), [WilsonLimits](GaplessYangMills/WilsonLimits.lean), [WilsonTranslations](GaplessYangMills/WilsonTranslations.lean) |
| §2 | The rank-one twist and cap gain, the cap probability in complex product coordinates, and the modified periodic Wilson partition comparison for conjugation-invariant twist laws. The comparison integrates the normal links as gauge averages and includes the spatial Boltzmann weights. Open bad-face events carry uniform bounds to weak limits. [RankOneTwist](GaplessYangMills/RankOneTwist.lean), [SphericalCap](GaplessYangMills/SphericalCap.lean), [GaugeAveraging](GaplessYangMills/GaugeAveraging.lean), [PeriodicWilsonComparison](GaplessYangMills/PeriodicWilsonComparison.lean), [BadEvents](GaplessYangMills/BadEvents.lean) |
| §3 | Principal eigenangles with multiplicity, closed integer defects, vanishing on all-good cubes at every rank, the marked-edge estimate conditional on the joint bad-face bound, and finite fillings with an explicit mass bound and square bases in a containing box. Locally finite component sums give a closed repaired flux. [Eigenangles](GaplessYangMills/Eigenangles.lean), [GoodCubes](GaplessYangMills/GoodCubes.lean), [MarkedEdges](GaplessYangMills/MarkedEdges.lean), [FiniteFilling](GaplessYangMills/FiniteFilling.lean), [Components](GaplessYangMills/Components.lean), [Gluing](GaplessYangMills/Gluing.lean) |
| §4 | The exact shift of the eigenangle lift and repaired flux under a central link rotation, the finite Haar change of variables, the finite log-weight derivative, and the zero-sum identity for compactly supported closed forms. [Eigenangles](GaplessYangMills/Eigenangles.lean), [FiniteWilson](GaplessYangMills/FiniteWilson.lean), [Action](GaplessYangMills/Action.lean), [Ward](GaplessYangMills/Ward.lean) |
| §5 | Contraction of a bounded-orbit symmetric shift in a positive reflection form, directional Cesàro projections and preservation of the Ward identities, removal of the full vacuum projection, and the conditional spectral obstruction. [TransferForm](GaplessYangMills/TransferForm.lean), [ShiftMeans](GaplessYangMills/ShiftMeans.lean), [DirectionalMean](GaplessYangMills/DirectionalMean.lean), [Spectral](GaplessYangMills/Spectral.lean), [Decay](GaplessYangMills/Decay.lean) |
| §6 | The local continuum curvature split, orthogonality in the trace norm, and extraction of the central curvature by the trace. [ContinuumSplit](GaplessYangMills/ContinuumSplit.lean) |

## Remaining proof obligations

- Connect the cap probability to the unitary rank-one twist distribution and apply the partition comparison to prove the joint bad-face bound.
- Prove the marked-component tails, almost-sure local finiteness, and the cut-uniform exponential approximation in (4).
- Prove the infinite-volume Gibbs formula and derive the integrable Ward response (5)–(8) for the Wilson state.
- Construct the reflection-positive Hilbert space and identify the Wilson transfer matrix elements. The resulting Ward and decay hypotheses would apply the checked `spectrum_near_one_of_ward` theorem to the Wilson transfer operator.
- Formalize the local plaquette spectral-weight conclusion and the continuum quantization statements under their respective hypotheses.
