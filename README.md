# Gaplessness of four-dimensional Wilson U(N) at weak coupling

[Read the paper](U-N-4D-mass-gap-proof.pdf).

This repository formalizes the fixed-spacing Wilson proof in Lean 4.
The theorem `wilson_transfer_gapless` proves that every periodic weak limit with `N ≥ 1` and
`β ≥ 10000` has spectrum in `(exp (-ε), 1)` for every `ε > 0` in each coordinate direction.
The theorem `wilson_transfer_positive_energies` gives the corresponding statement for `-log t`.
The theorem `wilson_plaquette_low_energy_spectrum` finds a single local plaquette current in each
time direction whose cyclic transfer spectrum meets every such interval.

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
| §1 | Cubical exterior derivatives, the periodic Wilson probability measure, existence of weak subsequential limits, and invariance under translations, axis permutations, coordinate reflections, and complex conjugation. The conditional Gibbs formula holds in finite volume and in every periodic weak limit for arbitrary finite link regions and measurable exterior tests. [Lattice](GaplessYangMills/Lattice.lean), [FiniteWilson](GaplessYangMills/FiniteWilson.lean), [FiniteGibbs](GaplessYangMills/FiniteGibbs.lean), [WilsonLimits](GaplessYangMills/WilsonLimits.lean), [WilsonTranslations](GaplessYangMills/WilsonTranslations.lean), [WilsonAxisPermutations](GaplessYangMills/WilsonAxisPermutations.lean), [WilsonReflections](GaplessYangMills/WilsonReflections.lean), [WilsonConjugation](GaplessYangMills/WilsonConjugation.lean), [InfiniteGibbs](GaplessYangMills/InfiniteGibbs.lean) |
| §2 | Lemma 2 for the periodic Wilson measures and their weak limits. The uniform rank-one twist law has the required cap probability and exponential gain. The modified partition comparison integrates the normal links as gauge averages and includes the spatial Boltzmann weights. [RankOneTwistLaw](GaplessYangMills/RankOneTwistLaw.lean), [GaugeAveraging](GaplessYangMills/GaugeAveraging.lean), [PeriodicWilsonComparison](GaplessYangMills/PeriodicWilsonComparison.lean), [WilsonBadPlaquettes](GaplessYangMills/WilsonBadPlaquettes.lean) |
| §3 | The joint marked-edge estimate (1), exponential marked-component size tails, and almost-sure finiteness of the components and their boxes at each vertex. The eigenangle lift gives closed integer defects and vanishes on all-good cubes after taking the exterior derivative. The finite component fillings give the measurable, almost surely closed repair (3), with a single error bound for all allowed cuts. Averaging the independent smooth cuts gives a closed, gauge-invariant, translation-covariant flux and bounded local approximants satisfying (4) at radius `4 * R + 4`. [GoodCubes](GaplessYangMills/GoodCubes.lean), [MarkedComponents](GaplessYangMills/MarkedComponents.lean), [MarkedBoxes](GaplessYangMills/MarkedBoxes.lean), [ComponentFlux](GaplessYangMills/ComponentFlux.lean), [CutFluxApproximation](GaplessYangMills/CutFluxApproximation.lean), [CutFluxBounds](GaplessYangMills/CutFluxBounds.lean), [CutAverages](GaplessYangMills/CutAverages.lean), [CutLaw](GaplessYangMills/CutLaw.lean), [FluxSymmetries](GaplessYangMills/FluxSymmetries.lean) |
| §4 | The Wilson and cut-density derivatives give (5) and (7) for the centered Wilson covariance and the translation-covariant response kernel, with the factor `1/N` from (5). Changing one cut affects the repaired flux inside a finite marked-component box almost surely. An integrable bound permits summation and integration of this change, giving absolute summability and zero total mass of the response in (6). The unprojected Wilson covariance is consequently nonsummable. [InfiniteAction](GaplessYangMills/InfiniteAction.lean), [CutResponseKernel](GaplessYangMills/CutResponseKernel.lean), [CutSensitivity](GaplessYangMills/CutSensitivity.lean), [CutNormalization](GaplessYangMills/CutNormalization.lean), [WilsonCovariance](GaplessYangMills/WilsonCovariance.lean) |
| §5 | The four commuting directional projections give the nonsummable covariance in (8). Site and bond reflection positivity construct the physical Wilson transfer, and its vacuum-subtracted matrix elements agree with the Euclidean directional projection. Axis permutations preserve the spectrum. The local flux approximants and plaquette currents give exponential covariance decay under a hypothetical gap, contradicting (8) and proving Theorem 1. Gaps on all six plaquette cyclic subspaces would give the same contradiction, yielding the local spectral-weight conclusion. [WilsonGapless](GaplessYangMills/WilsonGapless.lean), [WilsonPlaquetteSpectrum](GaplessYangMills/WilsonPlaquetteSpectrum.lean), [WilsonProjection](GaplessYangMills/WilsonProjection.lean), [WilsonOS](GaplessYangMills/WilsonOS.lean), [WilsonTransferCorrelations](GaplessYangMills/WilsonTransferCorrelations.lean), [WilsonAxisTransfer](GaplessYangMills/WilsonAxisTransfer.lean), [RealTransferSpectrum](GaplessYangMills/RealTransferSpectrum.lean) |
| §6 | The anti-Hermitian connection splits into a traceless connection and a central one-form. The curvature and trace action split, and the normalized trace extracts the central field strength. The quotient of `SU(N) × U(1)` has a cyclic kernel of order `N`. Its central phases cancel in the adjoint action, and the Wilson plaquette trace retains the phase. Smooth field-strength smearings give nonzero transverse Maxwell states in every small positive energy band. The Maxwell transfer and any product transfer that extends its action on the one-photon sector contain `exp (-E)` in their spectrum for every `E > 0`. [ContinuumSplit](GaplessYangMills/ContinuumSplit.lean), [UnitaryCenter](GaplessYangMills/UnitaryCenter.lean), [ContinuumMaxwell](GaplessYangMills/ContinuumMaxwell.lean) |

## Continuum scope

The continuum spectral conclusion is conditional on the paper's product quantization.
`maxwell_product_transfer_spectrum` expresses this premise with an isometric embedding of the
transverse one-photon Hilbert space that intertwines its transfer with the product transfer.
