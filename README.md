# Gaplessness of four-dimensional Wilson U(N) at weak coupling

At fixed lattice spacing, consider four-dimensional Wilson lattice gauge theory with gauge group U(N), for any positive integer N and any coupling of at least 10,000 in the paper’s normalization. For every infinite-volume weak limit of the periodic Wilson measures along even side lengths, the gauge-invariant transfer operator in each coordinate direction has spectral values arbitrarily close to one from below. This gives arbitrarily small positive transfer energies.

| Resource | Links |
| --- | --- |
| Paper | [PDF](U-N-4D-mass-gap-proof.pdf) |
| Lean 4 | [Theorem 1](GaplessYangMills/WilsonGapless.lean#L179) · [Formalization](GaplessYangMills) · [Proof audit](CheckProofs.lean) |

The Lean formalization uses Mathlib and contains no `sorry`, custom axioms, or `unsafe` declarations. The audit permits only Lean’s standard foundations `propext`, `Classical.choice`, and `Quot.sound`.

## Disclaimer

ChatGPT 6.2 Astra produced the current paper. I plan to work through the proof, rewrite the paper in my own voice, and give proper attribution to prior work.
