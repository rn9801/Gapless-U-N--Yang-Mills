module

public import GaplessYangMills.FiniteWilson
public import GaplessYangMills.KernelCycleEstimate
public import GaplessYangMills.TraceCycle
public import GaplessYangMills.WilsonKernel
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Product order for Wilson slice kernels

Sampling any finite collection of slices gives positive semidefinite matrices.
Schur products preserve the order as the indicated tangential links are twisted.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

def twistedFundamentalKernel {N : ℕ} (β : ℝ) (Z A B : UnitaryMatrix N) : ℝ :=
  fundamentalKernel β A B / 2 + fundamentalKernel β A (Z * B) / 4 +
    fundamentalKernel β A (Z⁻¹ * B) / 4

private theorem twistedFundamentalKernel_symm {N : ℕ} (β : ℝ) (Z A B : UnitaryMatrix N) :
    twistedFundamentalKernel β Z A B = twistedFundamentalKernel β Z B A := by
  have h (W : UnitaryMatrix N) :
      fundamentalKernel β A (W * B) = fundamentalKernel β B (W⁻¹ * A) := by
    have h' := fundamentalKernel_leftInvariant β W⁻¹ A (W * B)
    rw [← mul_assoc, inv_mul_cancel, one_mul, fundamentalKernel_symm β (W⁻¹ * A) B] at h'
    exact h'.symm
  rw [twistedFundamentalKernel, twistedFundamentalKernel, h Z, h Z⁻¹, inv_inv,
    fundamentalKernel_symm β A B]
  ring

private theorem quadratic_eq_sample {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (w : ι → ℝ) :
    star w ⬝ᵥ (M *ᵥ w) = kernelQuadratic Finset.univ w M := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
    kernelQuadratic]
  exact Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

private theorem posSemidef_sample {ι : Type*} [Fintype ι] (K : ι → ι → ℝ)
    (hs : ∀ i j, K i j = K j i)
    (h : ∀ w, 0 ≤ kernelQuadratic Finset.univ w K) : (Matrix.of K).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    exact hs j i
  · intro w
    rw [quadratic_eq_sample]
    exact h w

theorem fundamentalSample_order {N : ℕ} {ι : Type*} [Fintype ι] (β : ℝ) (hβ : 0 ≤ β)
    (A : ι → UnitaryMatrix N) (Z : UnitaryMatrix N) :
    let K := Matrix.of (fun i j => fundamentalKernel β (A i) (A j))
    let K' := Matrix.of (fun i j => twistedFundamentalKernel β Z (A i) (A j))
    K.PosSemidef ∧ K'.PosSemidef ∧ (K - K').PosSemidef := by
  dsimp
  have h (w : ι → ℝ) := fundamentalKernel_twist_bounds β hβ Finset.univ A w Z
  refine ⟨posSemidef_sample _ (fun i j => fundamentalKernel_symm β (A i) (A j))
    (fun w => wilsonKernel_nonneg (fun i => (A i).val) _ w β hβ),
    posSemidef_sample _ (fun i j => twistedFundamentalKernel_symm β Z (A i) (A j))
      (fun w => (h w).1), ?_⟩
  apply posSemidef_sample
  · intro i j
    exact congrArg₂ (· - ·) (fundamentalKernel_symm β (A i) (A j))
      (twistedFundamentalKernel_symm β Z (A i) (A j))
  · intro w
    change 0 ≤ kernelQuadratic Finset.univ w (fun i j =>
      fundamentalKernel β (A i) (A j) - twistedFundamentalKernel β Z (A i) (A j))
    have he : kernelQuadratic Finset.univ w (fun i j =>
        fundamentalKernel β (A i) (A j) - twistedFundamentalKernel β Z (A i) (A j)) =
      kernelQuadratic Finset.univ w (fun i j => fundamentalKernel β (A i) (A j)) -
      kernelQuadratic Finset.univ w (fun i j => twistedFundamentalKernel β Z (A i) (A j)) := by
      simp only [kernelQuadratic, mul_sub, Finset.sum_sub_distrib]
    rw [he]
    exact sub_nonneg.mpr (h w).2

private def sampleProduct {E ι : Type*} (K : E → Matrix ι ι ℝ) (s : Finset E) :
    Matrix ι ι ℝ := Matrix.of fun i j => ∏ e ∈ s, K e i j

private theorem sampleProduct_order {E ι : Type*} (s : Finset E)
    (K K' : E → Matrix ι ι ℝ)
    (h : ∀ e ∈ s, (K e).PosSemidef ∧ (K' e).PosSemidef ∧ (K e - K' e).PosSemidef) :
    (sampleProduct K s).PosSemidef ∧ (sampleProduct K' s).PosSemidef ∧
      (sampleProduct K s - sampleProduct K' s).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₁ : (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef := by
      let v : ι → ℝ := fun _ => 1
      have he : Matrix.of (fun _ _ : ι => (1 : ℝ)) = Matrix.vecMulVec v (star v) := by
        ext i j
        simp [Matrix.vecMulVec_apply, v]
      exact he ▸ Matrix.posSemidef_vecMulVec_self_star v
    simpa [sampleProduct, Matrix.PosSemidef.zero] using
      (show (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef ∧
        (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef from ⟨h₁, h₁⟩)
  | insert e s he ih =>
    have hprod (A : E → Matrix ι ι ℝ) :
        sampleProduct A (insert e s) = A e ⊙ sampleProduct A s := by
      ext i j
      exact Finset.prod_insert he
    rw [hprod, hprod]
    obtain ⟨hK, hK', hdiff⟩ := h e (Finset.mem_insert_self e s)
    obtain ⟨hs, hs', hsdiff⟩ := ih (fun f hf => h f (Finset.mem_insert_of_mem hf))
    refine ⟨hK.hadamard hs, hK'.hadamard hs', ?_⟩
    have heq : K e ⊙ sampleProduct K s - K' e ⊙ sampleProduct K' s =
        (K e - K' e) ⊙ sampleProduct K s +
          K' e ⊙ (sampleProduct K s - sampleProduct K' s) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.hadamard_apply, Matrix.add_apply]
      ring
    rw [heq]
    exact (hdiff.hadamard hs).add (hK'.hadamard hsdiff)

private theorem sampleProduct_select_order {E ι : Type*} [DecidableEq E]
    (s marked : Finset E) (U V₀ : E → Matrix ι ι ℝ)
    (hlocal : ∀ e ∈ s, (U e).PosSemidef ∧ (V₀ e).PosSemidef ∧ (U e - V₀ e).PosSemidef) :
    let K := sampleProduct U s
    let K' := Matrix.of fun i j => ∏ e ∈ s, if e ∈ marked then V₀ e i j else U e i j
    K.PosSemidef ∧ K'.PosSemidef ∧ (K - K').PosSemidef := by
  let V e := if e ∈ marked then V₀ e else U e
  have h := sampleProduct_order s U V (fun e hs => by
    have he := hlocal e hs
    by_cases hm : e ∈ marked
    · simpa only [V, ite_eq_left hm] using he
    · simpa only [V, ite_eq_right hm, sub_self, Matrix.PosSemidef.zero, and_true] using
        (show (U e).PosSemidef ∧ (U e).PosSemidef from ⟨he.1, he.1⟩))
  have hV : sampleProduct V s = Matrix.of (fun i j =>
      ∏ e ∈ s, if e ∈ marked then V₀ e i j else U e i j) := by
    ext i j
    apply Finset.prod_congr rfl
    intro e _
    by_cases hm : e ∈ marked <;> simp only [V, hm, ite_true, ite_false]
  rw [hV] at h
  exact h

/-- Applying twists independently to factors in a slice preserves the
positive order for every finite sample of slice configurations. -/
theorem fundamentalSliceSample_order {N : ℕ} {E ι : Type*} [Fintype ι] [DecidableEq E]
    (β : ℝ) (hβ : 0 ≤ β) (s : Finset E) (marked : Finset E)
    (A : ι → E → UnitaryMatrix N) (Z : E → UnitaryMatrix N) :
    let K := Matrix.of fun i j => ∏ e ∈ s, fundamentalKernel β (A i e) (A j e)
    let K' := Matrix.of fun i j => ∏ e ∈ s, if e ∈ marked then
      twistedFundamentalKernel β (Z e) (A i e) (A j e) else fundamentalKernel β (A i e) (A j e)
    K.PosSemidef ∧ K'.PosSemidef ∧ (K - K').PosSemidef :=
  sampleProduct_select_order s marked
    (fun e => Matrix.of fun i j => fundamentalKernel β (A i e) (A j e))
    (fun e => Matrix.of fun i j => twistedFundamentalKernel β (Z e) (A i e) (A j e))
    (fun e _ => fundamentalSample_order β hβ (fun i => A i e) (Z e))

/-- The finite trace comparison also holds after a common congruence of
the sampled kernels. A diagonal congruence inserts the slice weights. -/
theorem trace_fundamentalSliceSamples_le {N : ℕ} {E ι J : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq E] [Fintype J] [Nonempty J]
    (β : ℝ) (hβ : 0 ≤ β) (s : Finset E) (marked : J → Finset E)
    (A : ι → E → UnitaryMatrix N) (Z : J → E → UnitaryMatrix N)
    (D : Matrix ι ι ℝ) {n : ℕ} (hn : 0 < n) (w : List J) (hw : w.length = 2 * n) :
    let K := Matrix.of fun i j => ∏ e ∈ s, fundamentalKernel β (A i e) (A j e)
    let K' (t : J) := Matrix.of fun i j => ∏ e ∈ s, if e ∈ marked t then
      twistedFundamentalKernel β (Z t e) (A i e) (A j e) else fundamentalKernel β (A i e) (A j e)
    (w.map (fun t => Dᴴ * K' t * D)).prod.trace ≤ ((Dᴴ * K * D) ^ (2 * n)).trace := by
  intro K K'
  have horder (t : J) : (K' t).PosSemidef ∧ (K - K' t).PosSemidef :=
    (fundamentalSliceSample_order β hβ s (marked t) A (Z t)).2
  refine trace_even_word_le_reference (fun t => Dᴴ * K' t * D) (Dᴴ * K * D)
    (fun t => (horder t).1.conjTranspose_mul_mul_same D) ?_ hn w hw
  intro t
  simpa only [mul_sub, sub_mul] using (horder t).2.conjTranspose_mul_mul_same D

private theorem continuous_fundamentalKernel {N : ℕ} (β : ℝ) :
    Continuous (fun p : UnitaryMatrix N × UnitaryMatrix N => fundamentalKernel β p.1 p.2) := by
  have h : Continuous (fun p : UnitaryMatrix N × UnitaryMatrix N => (p.1 * p.2⁻¹).val) :=
    continuous_subtype_val.comp (continuous_fst.mul continuous_snd.inv)
  exact Real.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_re.comp (Continuous.matrix_trace h)))

private theorem continuous_twistedFundamentalKernel_all {N : ℕ} (β : ℝ) :
    Continuous (fun p : (UnitaryMatrix N × UnitaryMatrix N) × UnitaryMatrix N =>
      twistedFundamentalKernel β p.2 p.1.1 p.1.2) := by
  let U := UnitaryMatrix N
  let plus (p : (U × U) × U) : U × U := (p.1.1, p.2 * p.1.2)
  let minus (p : (U × U) × U) : U × U := (p.1.1, p.2⁻¹ * p.1.2)
  have hp : Continuous plus := continuous_fst.fst.prodMk (continuous_snd.mul continuous_fst.snd)
  have hm : Continuous minus := continuous_fst.fst.prodMk (continuous_snd.inv.mul continuous_fst.snd)
  have h := continuous_fundamentalKernel (N := N) β
  have h₀ : Continuous (fun p : (U × U) × U => fundamentalKernel β p.1.1 p.1.2) :=
    h.comp continuous_fst
  exact ((h₀.div_const 2).add ((h.comp hp).div_const 4)).add ((h.comp hm).div_const 4)

private theorem continuous_twistedFundamentalKernel {N : ℕ} (β : ℝ) (A B : UnitaryMatrix N) :
    Continuous (fun Z => twistedFundamentalKernel β Z A B) := by
  let U := UnitaryMatrix N
  let g (Z : U) : (U × U) × U := ((A, B), Z)
  have hg : Continuous g := continuous_const.prodMk continuous_id
  simpa only [Function.comp_def, g] using (continuous_twistedFundamentalKernel_all (N := N) β).comp hg

/-- The modified kernel averaged over a law of unitary twists. -/
def averagedFundamentalKernel {N : ℕ} (ν : Measure (UnitaryMatrix N))
    (β : ℝ) (A B : UnitaryMatrix N) : ℝ :=
  ∫ Z, twistedFundamentalKernel β Z A B ∂ν

private theorem continuous_averagedFundamentalKernel {N : ℕ} (ν : Measure (UnitaryMatrix N))
    [IsProbabilityMeasure ν] (β : ℝ) :
    Continuous (fun p : UnitaryMatrix N × UnitaryMatrix N => averagedFundamentalKernel ν β p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  have h := CompactSpace.uniformContinuous_of_continuous
    (continuous_twistedFundamentalKernel_all (N := N) β)
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuous_iff.mp h (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun q hq => ?_⟩
  have hint (a : UnitaryMatrix N × UnitaryMatrix N) :
      Integrable (fun Z => twistedFundamentalKernel β Z a.1 a.2) ν :=
    (continuous_twistedFundamentalKernel β a.1 a.2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [dist_eq_norm, averagedFundamentalKernel, averagedFundamentalKernel,
    ← integral_sub (hint q) (hint p)]
  have hbound (Z : UnitaryMatrix N) :
      ‖twistedFundamentalKernel β Z q.1 q.2 - twistedFundamentalKernel β Z p.1 p.2‖ ≤ ε / 2 := by
    have hx : dist (q, Z) (p, Z) < δ := by
      change max (dist q p) (dist Z Z) < δ
      rw [dist_self, max_lt_iff]
      exact ⟨hq, hδ⟩
    simpa only [dist_eq_norm] using (hu hx).le
  have hb := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hbound)
  exact (by simpa using hb : ‖∫ Z, twistedFundamentalKernel β Z q.1 q.2 -
    twistedFundamentalKernel β Z p.1 p.2 ∂ν‖ ≤ ε / 2).trans_lt (by linarith)

private theorem kernelQuadratic_integral {X ι : Type*} [MeasurableSpace X] {ν : Measure X}
    (s : Finset ι) (w : ι → ℝ) (K : X → ι → ι → ℝ)
    (h : ∀ i j, Integrable (fun x => K x i j) ν) :
    kernelQuadratic s w (fun i j => ∫ x, K x i j ∂ν) =
      ∫ x, kernelQuadratic s w (K x) ∂ν := by
  have hi (i j : ι) : Integrable (fun x => w i * w j * K x i j) ν := (h i j).const_mul _
  unfold kernelQuadratic
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum s (fun j _ => hi i j)]
  exact Finset.sum_congr rfl fun j _ => (integral_const_mul (w i * w j) _).symm

/-- Averaging the twists preserves the order for every finite sample. -/
theorem averagedFundamentalSample_order {N : ℕ} {ι : Type*} [Fintype ι]
    (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν] (β : ℝ) (hβ : 0 ≤ β)
    (A : ι → UnitaryMatrix N) :
    let K := Matrix.of (fun i j => fundamentalKernel β (A i) (A j))
    let K' := Matrix.of (fun i j => averagedFundamentalKernel ν β (A i) (A j))
    K.PosSemidef ∧ K'.PosSemidef ∧ (K - K').PosSemidef := by
  intro K K'
  have hsym (i j : ι) : averagedFundamentalKernel ν β (A i) (A j) =
      averagedFundamentalKernel ν β (A j) (A i) :=
    integral_congr_ae (Filter.Eventually.of_forall fun Z => twistedFundamentalKernel_symm β Z _ _)
  have hint (i j : ι) : Integrable (fun Z => twistedFundamentalKernel β Z (A i) (A j)) ν :=
    (continuous_twistedFundamentalKernel β (A i) (A j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h (w : ι → ℝ) := fun Z => fundamentalKernel_twist_bounds β hβ Finset.univ A w Z
  have he (w : ι → ℝ) : kernelQuadratic Finset.univ w (fun i j =>
      averagedFundamentalKernel ν β (A i) (A j)) =
      ∫ Z, kernelQuadratic Finset.univ w (fun i j => twistedFundamentalKernel β Z (A i) (A j)) ∂ν :=
    kernelQuadratic_integral _ _ _ hint
  have hupper (w : ι → ℝ) :
      kernelQuadratic Finset.univ w (fun i j => averagedFundamentalKernel ν β (A i) (A j)) ≤
        kernelQuadratic Finset.univ w (fun i j => fundamentalKernel β (A i) (A j)) := by
    rw [he]
    have hi : Integrable (fun Z => kernelQuadratic Finset.univ w
        (fun i j => twistedFundamentalKernel β Z (A i) (A j))) ν := by
      unfold kernelQuadratic
      exact integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => (hint i j).const_mul _))
    simpa using integral_mono hi (integrable_const _) (fun Z => (h w Z).2)
  refine ⟨posSemidef_sample _ (fun i j => fundamentalKernel_symm β _ _)
    (fun w => wilsonKernel_nonneg (fun i => (A i).val) _ w β hβ),
    posSemidef_sample _ hsym (fun w => (he w).symm ▸ integral_nonneg fun Z => (h w Z).1), ?_⟩
  apply posSemidef_sample
  · intro i j
    exact congrArg₂ (· - ·) (fundamentalKernel_symm β (A i) (A j)) (hsym i j)
  · intro w
    have hd : kernelQuadratic Finset.univ w
        (fun i j => fundamentalKernel β (A i) (A j) - averagedFundamentalKernel ν β (A i) (A j)) =
        kernelQuadratic Finset.univ w (fun i j => fundamentalKernel β (A i) (A j)) -
        kernelQuadratic Finset.univ w (fun i j => averagedFundamentalKernel ν β (A i) (A j)) := by
      simp only [kernelQuadratic, mul_sub, Finset.sum_sub_distrib]
    exact hd.symm ▸ sub_nonneg.mpr (hupper w)

/-- The finite trace comparison applies to the slice factors averaged over
the twist distribution. -/
theorem trace_averagedSliceSamples_le {N : ℕ} {E ι J : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq E] [Fintype J] [Nonempty J]
    (β : ℝ) (hβ : 0 ≤ β) (s : Finset E) (marked : J → Finset E)
    (A : ι → E → UnitaryMatrix N) (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν]
    (D : Matrix ι ι ℝ) {n : ℕ} (hn : 0 < n) (w : List J) (hw : w.length = 2 * n) :
    let K := Matrix.of fun i j => ∏ e ∈ s, fundamentalKernel β (A i e) (A j e)
    let K' (t : J) := Matrix.of fun i j => ∏ e ∈ s, if e ∈ marked t then
      averagedFundamentalKernel ν β (A i e) (A j e) else fundamentalKernel β (A i e) (A j e)
    (w.map (fun t => Dᴴ * K' t * D)).prod.trace ≤ ((Dᴴ * K * D) ^ (2 * n)).trace := by
  intro K K'
  have horder (t : J) : (K' t).PosSemidef ∧ (K - K' t).PosSemidef := by
    exact (sampleProduct_select_order s (marked t)
      (fun e => Matrix.of fun i j => fundamentalKernel β (A i e) (A j e))
      (fun e => Matrix.of fun i j => averagedFundamentalKernel ν β (A i e) (A j e))
      (fun e _ => averagedFundamentalSample_order ν β hβ (fun i => A i e))).2
  refine trace_even_word_le_reference (fun t => Dᴴ * K' t * D) (Dᴴ * K * D)
    (fun t => (horder t).1.conjTranspose_mul_mul_same D) ?_ hn w hw
  intro t
  simpa only [mul_sub, sub_mul] using (horder t).2.conjTranspose_mul_mul_same D

/-- The unprojected Wilson slice comparison with a continuous spatial
weight and averaged twists. Each normal-link gauge average is a separate
operation on these kernels. -/
theorem kernelCycleIntegral_averagedWilsonSlices_le {N : ℕ} {E J : Type*}
    [Fintype E] [DecidableEq E] [Fintype J] [Nonempty J]
    (β : ℝ) (hβ : 0 ≤ β) (s : Finset E) (marked : J → Finset E)
    (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν]
    (μ : Measure (E → UnitaryMatrix N)) [IsProbabilityMeasure μ]
    (w : (E → UnitaryMatrix N) → ℝ) (hw : Continuous w)
    (j : J) (js : List J) {n : ℕ} (hn : 0 < n) (hlen : (j :: js).length = 2 * n) :
    let K₀ (a b : E → UnitaryMatrix N) :=
      w a * (∏ e ∈ s, fundamentalKernel β (a e) (b e)) * w b
    let K (t : J) (a b : E → UnitaryMatrix N) :=
      w a * (∏ e ∈ s, if e ∈ marked t then averagedFundamentalKernel ν β (a e) (b e)
        else fundamentalKernel β (a e) (b e)) * w b
    kernelCycleIntegral μ (K j) (js.map K) ≤
      kernelCycleIntegral μ K₀ (List.replicate js.length K₀) := by
  intro K₀ K
  let X := E → UnitaryMatrix N
  have he (e : E) : Continuous (fun p : X × X => (p.1 e, p.2 e)) :=
    ((continuous_apply e).comp continuous_fst).prodMk ((continuous_apply e).comp continuous_snd)
  have hc₀ : Continuous (fun p : X × X => K₀ p.1 p.2) := by
    exact ((hw.comp continuous_fst).mul (continuous_finsetProd s (fun e _ =>
      (continuous_fundamentalKernel β).comp (he e)))).mul (hw.comp continuous_snd)
  have hct (t : J) : Continuous (fun p : X × X => K t p.1 p.2) := by
    have hs : Continuous (fun p : X × X => ∏ e ∈ s, if e ∈ marked t then
        averagedFundamentalKernel ν β (p.1 e) (p.2 e) else fundamentalKernel β (p.1 e) (p.2 e)) := by
      apply continuous_finsetProd s
      intro e _
      by_cases hm : e ∈ marked t
      · simpa only [ite_eq_left hm, Function.comp_def] using (continuous_averagedFundamentalKernel ν β).comp (he e)
      · simpa only [ite_eq_right hm, Function.comp_def] using (continuous_fundamentalKernel β).comp (he e)
    exact ((hw.comp continuous_fst).mul hs).mul (hw.comp continuous_snd)
  have horder (m : ℕ) (v : Fin m → X) (t : J) :
      (Matrix.of fun a b => K t (v a) (v b)).PosSemidef ∧
        ((Matrix.of fun a b => K₀ (v a) (v b)) -
          (Matrix.of fun a b => K t (v a) (v b))).PosSemidef := by
    let U e := Matrix.of fun a b => fundamentalKernel β (v a e) (v b e)
    let V e := Matrix.of fun a b => averagedFundamentalKernel ν β (v a e) (v b e)
    let D := Matrix.diagonal fun a : Fin m => w (v a)
    have hD : Dᴴ = D := by simp [D]
    let K₁ := Matrix.of fun a b => ∏ e ∈ s, if e ∈ marked t then V e a b else U e a b
    have hraw : K₁.PosSemidef ∧ (sampleProduct U s - K₁).PosSemidef :=
      (sampleProduct_select_order s (marked t) U V
        (fun e _ => averagedFundamentalSample_order ν β hβ (fun a => v a e))).2
    have hmul (M : Matrix (Fin m) (Fin m) ℝ) : D * M * D =
        Matrix.of (fun a b => w (v a) * M a b * w (v b)) := by
      ext a b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    have hs₀ : D * sampleProduct U s * D = Matrix.of (fun a b => K₀ (v a) (v b)) :=
      hmul _
    have hs₁ : D * K₁ * D = Matrix.of (fun a b => K t (v a) (v b)) :=
      hmul _
    refine ⟨?_, ?_⟩
    · simpa only [hD, hs₁] using hraw.1.conjTranspose_mul_mul_same D
    · simpa only [hD, mul_sub, sub_mul, hs₀, hs₁] using hraw.2.conjTranspose_mul_mul_same D
  exact kernelCycleIntegral_le_of_sampleOrder μ K K₀ hct hc₀
    (fun m v t => (horder m v t).1) (fun m v t => (horder m v t).2) j js hn hlen

end

end GaplessYangMills
