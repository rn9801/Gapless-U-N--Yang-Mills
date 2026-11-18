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
| §1 | Cubical exterior derivatives, the periodic Wilson probability measure, existence of weak subsequential limits, and invariance under translations and coordinate reflections. The conditional Gibbs formula holds in finite volume and in every periodic weak limit for arbitrary finite link regions and measurable exterior tests. [Lattice](GaplessYangMills/Lattice.lean), [FiniteWilson](GaplessYangMills/FiniteWilson.lean), [FiniteGibbs](GaplessYangMills/FiniteGibbs.lean), [WilsonLimits](GaplessYangMills/WilsonLimits.lean), [WilsonTranslations](GaplessYangMills/WilsonTranslations.lean), [WilsonReflections](GaplessYangMills/WilsonReflections.lean), [InfiniteGibbs](GaplessYangMills/InfiniteGibbs.lean) |
| §2 | Lemma 2 for the periodic Wilson measures and their weak limits. The uniform rank-one twist law has the required cap probability and exponential gain. The modified partition comparison integrates the normal links as gauge averages and includes the spatial Boltzmann weights. [RankOneTwistLaw](GaplessYangMills/RankOneTwistLaw.lean), [GaugeAveraging](GaplessYangMills/GaugeAveraging.lean), [PeriodicWilsonComparison](GaplessYangMills/PeriodicWilsonComparison.lean), [WilsonBadPlaquettes](GaplessYangMills/WilsonBadPlaquettes.lean) |
| §3 | The joint marked-edge estimate (1), exponential marked-component size tails, and almost-sure finiteness of the components and their boxes at each vertex. The eigenangle lift gives closed integer defects and vanishes on all-good cubes after taking the exterior derivative. The finite component fillings give the measurable, almost surely closed repair (3), with a single error bound for all allowed cuts. Averaging the independent smooth cuts gives a closed, gauge-invariant, translation-covariant flux and bounded local approximants satisfying (4) at radius `4 * R + 4`. [GoodCubes](GaplessYangMills/GoodCubes.lean), [MarkedComponents](GaplessYangMills/MarkedComponents.lean), [MarkedBoxes](GaplessYangMills/MarkedBoxes.lean), [ComponentFlux](GaplessYangMills/ComponentFlux.lean), [CutFluxApproximation](GaplessYangMills/CutFluxApproximation.lean), [CutFluxBounds](GaplessYangMills/CutFluxBounds.lean), [CutAverages](GaplessYangMills/CutAverages.lean), [CutLaw](GaplessYangMills/CutLaw.lean), [FluxSymmetries](GaplessYangMills/FluxSymmetries.lean) |
| §4 | The Wilson and cut-density derivatives give (5) and (7) for the centered Wilson covariance and the translation-covariant response kernel, with the factor `1/N` from (5). Changing one cut affects the repaired flux inside a finite marked-component box almost surely. An integrable bound permits summation and integration of this change, giving absolute summability and zero total mass of the response in (6). The unprojected Wilson covariance is consequently nonsummable. [InfiniteAction](GaplessYangMills/InfiniteAction.lean), [CutResponseKernel](GaplessYangMills/CutResponseKernel.lean), [CutSensitivity](GaplessYangMills/CutSensitivity.lean), [CutNormalization](GaplessYangMills/CutNormalization.lean), [WilsonCovariance](GaplessYangMills/WilsonCovariance.lean) |
| §5 | The four commuting directional projections in the Wilson state's Euclidean `L²` give the nonsummable covariance in (8). Site and bond reflection positivity hold on every even torus of side at least four, and pass to continuous positive-time cylinder observables in the weak limits. Bond positivity uses gauge fixing of the two seam matchings and positivity of the resulting fundamental Gram kernel. Completion of a positive reflection form gives a Hilbert space and a positive self-adjoint transfer contraction from a bounded-orbit shift. [WilsonProjection](GaplessYangMills/WilsonProjection.lean), [PeriodicSiteReflection](GaplessYangMills/PeriodicSiteReflection.lean), [PeriodicBondReflection](GaplessYangMills/PeriodicBondReflection.lean), [WilsonBondLimit](GaplessYangMills/WilsonBondLimit.lean), [ReflectionHilbert](GaplessYangMills/ReflectionHilbert.lean), [Spectral](GaplessYangMills/Spectral.lean), [Decay](GaplessYangMills/Decay.lean) |
| §6 | The local continuum curvature split, orthogonality in the trace norm, and extraction of the central curvature by the trace. [ContinuumSplit](GaplessYangMills/ContinuumSplit.lean) |

## Remaining proof obligations

- Extend the reflection form by `L²` approximation and identify the Wilson transfer matrix elements. The resulting Ward and decay hypotheses would apply the checked `spectrum_near_one_of_ward` theorem to the Wilson transfer operator.
- Formalize the local plaquette spectral-weight conclusion and the continuum quantization statements under their respective hypotheses.
