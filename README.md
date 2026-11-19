# Gaplessness of four-dimensional Wilson U(N) at weak coupling

**Theorem.** In four-dimensional Wilson $U(N)$ lattice gauge theory at fixed lattice spacing,
the gauge-invariant Hamiltonian in each coordinate direction has spectrum intersecting
$(0,\epsilon)$ for every $\epsilon > 0$. This holds for every positive integer $N$, every Wilson
coupling $\beta$ of at least 10,000 in the paper’s normalization, and every infinite-volume weak
limit of the periodic Wilson measures along even side lengths.

Equivalently, in each direction there is no positive exponential decay rate that holds uniformly
for all gauge-invariant time correlations after subtracting the contribution of the entire vacuum
space.

| Resource | Links |
| --- | --- |
| Paper | [PDF](U-N-4D-mass-gap-proof.pdf) |
| Lean 4 | [Theorem 1](GaplessYangMills/WilsonGapless.lean#L179) · [Formalization](GaplessYangMills) · [Proof audit](CheckProofs.lean) |

The Lean formalization uses Mathlib and contains no `sorry`, custom axioms, or `unsafe` declarations. The audit permits only Lean’s standard foundations `propext`, `Classical.choice`, and `Quot.sound`.

## Disclaimer

ChatGPT 6.2 Astra produced the current paper. I plan to work through the proof, rewrite the paper in my own voice, and give proper attribution to prior work.
