module

public import GaplessYangMills.FiniteWilson
public import GaplessYangMills.GaugeAveraging
public import GaplessYangMills.KernelCycleEstimate
public import GaplessYangMills.TraceCycle
public import GaplessYangMills.WilsonKernel
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.Group

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

theorem continuous_fundamentalKernel {N : ℕ} (β : ℝ) :
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

theorem continuous_twistedFundamentalKernel {N : ℕ} (β : ℝ) (A B : UnitaryMatrix N) :
    Continuous (fun Z => twistedFundamentalKernel β Z A B) := by
  let U := UnitaryMatrix N
  let g (Z : U) : (U × U) × U := ((A, B), Z)
  have hg : Continuous g := continuous_const.prodMk continuous_id
  simpa only [Function.comp_def, g] using (continuous_twistedFundamentalKernel_all (N := N) β).comp hg

/-- The modified kernel averaged over a law of unitary twists. -/
def averagedFundamentalKernel {N : ℕ} (ν : Measure (UnitaryMatrix N))
    (β : ℝ) (A B : UnitaryMatrix N) : ℝ :=
  ∫ Z, twistedFundamentalKernel β Z A B ∂ν

theorem continuous_averagedFundamentalKernel {N : ℕ} (ν : Measure (UnitaryMatrix N))
    [IsProbabilityMeasure ν] (β : ℝ) :
    Continuous (fun p : UnitaryMatrix N × UnitaryMatrix N => averagedFundamentalKernel ν β p.1 p.2) := by
  exact continuous_integral_parameter ν (continuous_twistedFundamentalKernel_all β)

theorem averagedFundamentalKernel_symm {N : ℕ} (ν : Measure (UnitaryMatrix N)) (β : ℝ)
    (A B : UnitaryMatrix N) :
    averagedFundamentalKernel ν β A B = averagedFundamentalKernel ν β B A := by
  simp only [averagedFundamentalKernel]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun Z =>
    twistedFundamentalKernel_symm β Z A B))

theorem averagedFundamentalKernel_rightInvariant {N : ℕ} (ν : Measure (UnitaryMatrix N))
    (β : ℝ) (Q A B : UnitaryMatrix N) :
    averagedFundamentalKernel ν β (A * Q) (B * Q) = averagedFundamentalKernel ν β A B := by
  simp only [averagedFundamentalKernel, twistedFundamentalKernel,
    ← mul_assoc, fundamentalKernel_rightInvariant]

theorem averagedFundamentalKernel_leftInvariant {N : ℕ} (ν : Measure (UnitaryMatrix N))
    (hν : ∀ Q : UnitaryMatrix N, MeasurePreserving (fun Z => Q * Z * Q⁻¹) ν ν)
    (β : ℝ) (Q A B : UnitaryMatrix N) :
    averagedFundamentalKernel ν β (Q * A) (Q * B) = averagedFundamentalKernel ν β A B := by
  have hZ (Z : UnitaryMatrix N) :
      twistedFundamentalKernel β (Q * Z * Q⁻¹) (Q * A) (Q * B) =
        twistedFundamentalKernel β Z A B := by
    have hplus : (Q * Z * Q⁻¹) * (Q * B) = Q * (Z * B) := by group
    have hminus : (Q * Z * Q⁻¹)⁻¹ * (Q * B) = Q * (Z⁻¹ * B) := by group
    simp only [twistedFundamentalKernel, hplus, hminus, fundamentalKernel_leftInvariant]
  unfold averagedFundamentalKernel
  have hcomp := integral_map (μ := ν) (hν Q).measurable.aemeasurable
    (continuous_twistedFundamentalKernel β (Q * A) (Q * B)).aestronglyMeasurable
  rw [(hν Q).map_eq] at hcomp
  rw [hcomp]
  exact integral_congr_ae (Filter.Eventually.of_forall hZ)

theorem averagedFundamentalKernel_pos {N : ℕ} (ν : Measure (UnitaryMatrix N))
    [IsProbabilityMeasure ν] (β : ℝ) (A B : UnitaryMatrix N) :
    0 < averagedFundamentalKernel ν β A B := by
  have hint : Integrable (fun Z => twistedFundamentalKernel β Z A B) ν :=
    (continuous_twistedFundamentalKernel β A B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono (integrable_const (μ := ν) (fundamentalKernel β A B / 2))
    hint (fun Z => by
      unfold twistedFundamentalKernel
      linarith [fundamentalKernel_pos β A (Z * B), fundamentalKernel_pos β A (Z⁻¹ * B)])
  have hb : fundamentalKernel β A B / 2 ≤ averagedFundamentalKernel ν β A B := by
    simpa only [averagedFundamentalKernel, integral_const, probReal_univ, one_smul] using h
  exact (half_pos (fundamentalKernel_pos β A B)).trans_le hb

/-- The ratio of the modified and unmodified factors at a plaquette. -/
def wilsonTwistMultiplier {N : ℕ} (ν : Measure (UnitaryMatrix N)) (β : ℝ)
    (P : UnitaryMatrix N) : ℝ :=
  averagedFundamentalKernel ν β P 1 / fundamentalKernel β P 1

theorem wilsonTwistMultiplier_pos {N : ℕ} (ν : Measure (UnitaryMatrix N))
    [IsProbabilityMeasure ν] (β : ℝ) (P : UnitaryMatrix N) :
    0 < wilsonTwistMultiplier ν β P :=
  div_pos (averagedFundamentalKernel_pos ν β P 1) (fundamentalKernel_pos β P 1)

theorem continuous_wilsonTwistMultiplier {N : ℕ} (ν : Measure (UnitaryMatrix N))
    [IsProbabilityMeasure ν] (β : ℝ) : Continuous (wilsonTwistMultiplier ν β) := by
  have hP : Continuous (fun P : UnitaryMatrix N => (P, (1 : UnitaryMatrix N))) :=
    continuous_id.prodMk continuous_const
  have hn : Continuous (fun P : UnitaryMatrix N => averagedFundamentalKernel ν β P 1) := by
    simpa only [Function.comp_def] using (continuous_averagedFundamentalKernel ν β).comp hP
  have hd : Continuous (fun P : UnitaryMatrix N => fundamentalKernel β P 1) := by
    simpa only [Function.comp_def] using (continuous_fundamentalKernel (N := N) β).comp hP
  unfold wilsonTwistMultiplier
  exact hn.div hd (fun P => (fundamentalKernel_pos β P 1).ne')

theorem fundamentalKernel_mul_wilsonTwistMultiplier {N : ℕ} (ν : Measure (UnitaryMatrix N))
    (β : ℝ) (A B : UnitaryMatrix N) :
    fundamentalKernel β A B * wilsonTwistMultiplier ν β (A * B⁻¹) =
      averagedFundamentalKernel ν β A B := by
  have h := fundamentalKernel_rightInvariant β B⁻¹ A B
  have h' := averagedFundamentalKernel_rightInvariant ν β B⁻¹ A B
  rw [mul_inv_cancel] at h h'
  rw [wilsonTwistMultiplier, h, h', mul_div_cancel₀ _ (fundamentalKernel_pos β A B).ne']

theorem wilsonTwistMultiplier_inv {N : ℕ} (ν : Measure (UnitaryMatrix N)) (β : ℝ)
    (P : UnitaryMatrix N) : wilsonTwistMultiplier ν β P⁻¹ = wilsonTwistMultiplier ν β P := by
  have h := fundamentalKernel_rightInvariant β P P⁻¹ 1
  have h' := averagedFundamentalKernel_rightInvariant ν β P P⁻¹ 1
  simp only [inv_mul_cancel, one_mul] at h h'
  rw [wilsonTwistMultiplier, ← h, ← h', fundamentalKernel_symm β 1 P,
    averagedFundamentalKernel_symm ν β 1 P]
  rfl

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

/-- The product of the single-link kernels, modified at the selected links. -/
def averagedWilsonSlice {N : ℕ} {E : Type*} [DecidableEq E]
    (ν : Measure (UnitaryMatrix N)) (β : ℝ) (s marked : Finset E)
    (a b : E → UnitaryMatrix N) : ℝ :=
  ∏ e ∈ s, if e ∈ marked then averagedFundamentalKernel ν β (a e) (b e)
    else fundamentalKernel β (a e) (b e)

theorem continuous_averagedWilsonSlice {N : ℕ} {E : Type*} [DecidableEq E]
    (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν] (β : ℝ) (s marked : Finset E) :
    Continuous (fun p : (E → UnitaryMatrix N) × (E → UnitaryMatrix N) =>
      averagedWilsonSlice ν β s marked p.1 p.2) := by
  unfold averagedWilsonSlice
  apply continuous_finsetProd
  intro e _
  have he : Continuous (fun p : (E → UnitaryMatrix N) × (E → UnitaryMatrix N) =>
      (p.1 e, p.2 e)) :=
    ((continuous_apply e).comp continuous_fst).prodMk ((continuous_apply e).comp continuous_snd)
  by_cases hm : e ∈ marked
  · simpa only [ite_eq_left hm, Function.comp_def] using
      (continuous_averagedFundamentalKernel ν β).comp he
  · simpa only [ite_eq_right hm, Function.comp_def] using
      (continuous_fundamentalKernel β).comp he

theorem averagedWilsonSlice_positive_order {N : ℕ} {E : Type*} [DecidableEq E]
    (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν] (β : ℝ) (hβ : 0 ≤ β)
    (s marked : Finset E) :
    PositiveKernel (averagedWilsonSlice ν β s marked) ∧
      PositiveKernel (fun a b => averagedWilsonSlice ν β s ∅ a b -
        averagedWilsonSlice ν β s marked a b) := by
  have h (m : ℕ) (v : Fin m → E → UnitaryMatrix N) :=
    sampleProduct_select_order s marked
      (fun e => Matrix.of fun a b => fundamentalKernel β (v a e) (v b e))
      (fun e => Matrix.of fun a b => averagedFundamentalKernel ν β (v a e) (v b e))
      (fun e _ => averagedFundamentalSample_order ν β hβ (fun a => v a e))
  refine ⟨fun m v => (h m v).2.1, fun m v => ?_⟩
  have hdiff := (h m v).2.2
  convert hdiff using 1
  ext i j
  simp [sampleProduct, averagedWilsonSlice]

/-- The unprojected Wilson slice comparison with a continuous spatial
weight and averaged twists. -/
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
  have h₀ : weightedKernel w (averagedWilsonSlice ν β s ∅) = K₀ := by
    funext a b
    simp [weightedKernel, averagedWilsonSlice, K₀]
  have hc₀ := continuous_weightedKernel hw (continuous_averagedWilsonSlice ν β s ∅)
  rw [h₀] at hc₀
  refine kernelCycleIntegral_le_of_sampleOrder μ K K₀
    (fun t => continuous_weightedKernel hw (continuous_averagedWilsonSlice ν β s (marked t)))
    hc₀ (fun m v t => ((averagedWilsonSlice_positive_order ν β hβ s (marked t)).1.weighted w) m v)
    (fun m v t => ?_) j js hn hlen
  have h := ((averagedWilsonSlice_positive_order ν β hβ s (marked t)).2.weighted w) m v
  convert h using 1
  ext a b
  rw [Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, weightedKernel_sub, h₀]
  rfl

end

end GaplessYangMills
