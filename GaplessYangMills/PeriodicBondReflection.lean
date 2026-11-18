module

public import GaplessYangMills.BondSeams
public import GaplessYangMills.PeriodicSiteReflection
public import GaplessYangMills.WilsonSliceKernel

/-!
# Bond reflection positivity of the periodic Wilson measure

After fixing the two seam matchings to identity, the crossing plaquettes
give the product of the fundamental positive kernels. The two remaining
actions are the same half-action on independent Haar variables.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

noncomputable section

private abbrev SeamCell (L : ℕ) {J : Type*} (τ : Axis) (normal : J → Bool) :=
  {p // bondCutBoundary (L := L) τ normal p}

private abbrev BondInteriorCell (L : ℕ) {J : Type*} (τ : Axis) (normal : J → Bool) :=
  {p // bondCutInterior (L := L) τ normal p}

private abbrev BondHalf (L N : ℕ) (τ : Axis) :=
  BondInteriorCell L τ (normalLink τ) → UnitaryMatrix N

private abbrev SeamValues (L N : ℕ) (τ : Axis) :=
  SeamCell L τ (normalLink τ) → UnitaryMatrix N

attribute [local instance] Fintype.ofFinite

private def bondFullAssembly {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L) (τ : Axis) :
    SeamValues L N τ × (BondHalf L N τ × BondHalf L N τ) → TorusConfig L N :=
  assembleReflection (bondCutCellEquiv hL he τ (normalLink τ)) (fun p => normalLink τ p.val.1)

private def bondAssembly {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L) (τ : Axis)
    (q : BondHalf L N τ × BondHalf L N τ) : TorusConfig L N :=
  bondFullAssembly hL he τ (1, q)

private theorem continuous_bondAssembly {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L) (τ : Axis) :
    Continuous (bondAssembly (N := N) hL he τ) :=
  (continuous_assembleReflection _ _).comp (continuous_const.prodMk continuous_id)

private theorem bondAssembly_seam {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L) (τ : Axis)
    (q : BondHalf L N τ × BondHalf L N τ) (p : SeamCell L τ (normalLink τ)) :
    bondAssembly hL he τ q p.val = 1 :=
  assembleReflection_boundary (bondCutCellEquiv hL he τ (normalLink τ)) _ _ p

private theorem bondAssembly_positive {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L) (τ : Axis)
    (q : BondHalf L N τ × BondHalf L N τ) (p : BondInteriorCell L τ (normalLink τ)) :
    bondAssembly hL he τ q p.val = q.1 p :=
  assembleReflection_positive (bondCutCellEquiv hL he τ (normalLink τ)) _ _ p

private theorem bondAssembly_negative {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L) (τ : Axis)
    (q : BondHalf L N τ × BondHalf L N τ) (p : BondInteriorCell L τ (normalLink τ)) :
    bondAssembly hL he τ q (bondReflectCell τ (normalLink τ) p.val) =
      if normalLink τ p.val.1 then (q.2 p)⁻¹ else q.2 p :=
  assembleReflection_negative (bondCutCellEquiv hL he τ (normalLink τ)) _ _ p

private theorem bondAssembly_reflect {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L) (τ : Axis)
    (q : BondHalf L N τ × BondHalf L N τ) :
    reflectPeriodic τ (-1) (bondAssembly hL he τ q) = bondAssembly hL he τ (q.2, q.1) := by
  let r := bondReflectCell (L := L) τ (normalLink τ)
  have hrefl (U : TorusConfig L N) (p : TorusLink L) :
      reflectPeriodic τ (-1) U p = if normalLink τ p.1 then (U (r p))⁻¹ else U (r p) := by
    by_cases hp : p.1 = τ <;> simp [reflectPeriodic, reflectLinksOn, normalLink, hp, r, reflectLinkIndex_bond]
  funext p
  obtain ⟨v, rfl⟩ := (bondCutCellEquiv hL he τ (normalLink τ)).surjective p
  rcases v with b | p | p
  · change reflectPeriodic τ (-1) (bondAssembly hL he τ q) b.val =
      bondAssembly hL he τ (q.2, q.1) b.val
    rw [hrefl, show r b.val = b.val from bondReflectCell_boundary hL he τ _ _ b.property,
      bondAssembly_seam, bondAssembly_seam]
    simp
  · change reflectPeriodic τ (-1) (bondAssembly hL he τ q) p.val =
      bondAssembly hL he τ (q.2, q.1) p.val
    rw [hrefl, show r p.val = bondReflectCell τ (normalLink τ) p.val from rfl,
      bondAssembly_negative, bondAssembly_positive]
    by_cases hn : normalLink τ p.val.1 <;> simp [hn]
  · change reflectPeriodic τ (-1) (bondAssembly hL he τ q) (r p.val) =
      bondAssembly hL he τ (q.2, q.1) (bondReflectCell τ (normalLink τ) p.val)
    rw [hrefl, show r (r p.val) = p.val from bondReflectCell_involutive τ _ _,
      bondAssembly_positive, bondAssembly_negative]
    rfl

private def bondHalfHaar {L N : ℕ} [NeZero L] (τ : Axis) : Measure (BondHalf L N τ) :=
  Measure.pi fun _ => unitaryHaar N

private instance bondHalfHaar_probability {L N : ℕ} [NeZero L] (τ : Axis) :
    IsProbabilityMeasure (bondHalfHaar (L := L) (N := N) τ) := by
  unfold bondHalfHaar
  infer_instance

private theorem integral_exterior_bondAssembly {L N : ℕ} [NeZero L] (hL : 4 ≤ L)
    (he : 2 * (L / 2) = L) (τ : Axis) (f : TorusConfig L N → ℝ) (hf : Measurable f) :
    (∫ b, f ((splitPeriodicLinks (bondSeamLinks L τ)).symm (1, b)) ∂exteriorHaar (bondSeamLinks L τ)) =
      ∫ q, f (bondAssembly hL he τ q) ∂(bondHalfHaar τ).prod (bondHalfHaar τ) := by
  let Λ := bondSeamLinks L τ
  let U := bondFullAssembly (N := N) hL he τ
  let E := splitPeriodicLinks (N := N) Λ
  let m : Measure (BondHalf L N τ) := bondHalfHaar τ
  let b : Measure (SeamValues L N τ) := Measure.pi fun _ => unitaryHaar N
  let Q (q : BondHalf L N τ × BondHalf L N τ) (p : {p // p ∉ Λ}) := bondAssembly hL he τ q p.val
  have hQ : Measurable Q :=
    measurable_pi_iff.mpr fun p => (continuous_apply p.val).measurable.comp
      (continuous_bondAssembly hL he τ).measurable
  have hU : MeasurePreserving U (b.prod (m.prod m)) (periodicHaar L N) :=
    measurePreserving_assembleReflection _ _
  have hE := (measurePreserving_snd (μ := blockHaar (N := N) Λ) (ν := exteriorHaar Λ)).comp
    (splitPeriodicLinks_preserving (N := N) Λ)
  have hC := hE.comp hU
  have hEq : (Prod.snd ∘ ⇑E) ∘ U = Q ∘ Prod.snd := by
    funext q p
    have h := joinPeriodic_eq_exterior (E (U q)).1 (E (U q)).2 p.property
    rw [E.symm_apply_apply] at h
    change (E (U q)).2 p = Q q.2 p
    rw [← h]
    let e := bondCutCellEquiv hL he τ (normalLink τ)
    obtain ⟨v, hv⟩ := e.surjective p.val
    change assembleReflection e _ q p.val = assembleReflection e _ (1, q.2) p.val
    rw [← hv]
    rcases v with k | k | k
    · have hk : k.val = p.val := hv
      exact (p.property ((mem_bondSeamLinks τ p.val).mpr (hk ▸ k.property))).elim
    · rw [assembleReflection_positive, assembleReflection_positive]
    · rw [assembleReflection_negative, assembleReflection_negative]
  have hp : MeasurePreserving Q (m.prod m) (exteriorHaar Λ) := by
    refine ⟨hQ, ?_⟩
    have hS : MeasurePreserving Prod.snd (b.prod (m.prod m)) (m.prod m) :=
      measurePreserving_snd
    rw [← hS.map_eq, Measure.map_map hQ measurable_snd, ← hEq, hC.map_eq]
  have hjoin (q : BondHalf L N τ × BondHalf L N τ) : E.symm (1, Q q) = bondAssembly hL he τ q := by
    funext p
    by_cases h : p ∈ Λ
    · rw [joinPeriodic_eq_block 1 (Q q) h]
      exact (bondAssembly_seam hL he τ q ⟨p, (mem_bondSeamLinks τ p).mp h⟩).symm
    · exact joinPeriodic_eq_exterior 1 (Q q) h
  let F (p : PeriodicExterior N Λ) := f (E.symm (1, p))
  have hF : Measurable F := hf.comp (E.symm.measurable.comp (measurable_const.prodMk measurable_id))
  change (∫ p, F p ∂exteriorHaar Λ) = _
  rw [← hp.map_eq, integral_map hQ.aemeasurable hF.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun q => congrArg f (hjoin q))

private def bondSeamAction {L N : ℕ} [NeZero L] (τ : Axis) (β : ℝ) (U : TorusConfig L N) : ℝ :=
  (N : ℝ) * β * ∑ p : SeamCell L τ (normalFace τ), (periodicHolonomy U p.val.1 p.val.2).val.trace.re

private def bondInteriorAction {L N : ℕ} [NeZero L] (τ : Axis) (β : ℝ) (U : TorusConfig L N) : ℝ :=
  (N : ℝ) * β * ∑ p : BondInteriorCell L τ (normalFace τ), (periodicHolonomy U p.val.1 p.val.2).val.trace.re

private theorem continuous_bondInteriorAction {L N : ℕ} [NeZero L] (τ : Axis) (β : ℝ) :
    Continuous (bondInteriorAction τ β : TorusConfig L N → ℝ) := by
  unfold bondInteriorAction
  apply continuous_const.mul
  exact continuous_finsetSum _ fun p _ => Complex.continuous_re.comp
    (Continuous.matrix_trace (continuous_subtype_val.comp (continuous_periodicHolonomy p.val.1 p.val.2)))

private theorem bondCut_action_split {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L)
    (τ : Axis) (β : ℝ) (U : TorusConfig L N) :
    periodicLogWeight β U = bondSeamAction τ β U +
      bondInteriorAction τ β U + bondInteriorAction τ β (reflectPeriodic τ (-1) U) := by
  let e := bondCutCellEquiv hL he τ (normalFace τ)
  let f (p : Face × TorusSite L) := (periodicHolonomy U p.1 p.2).val.trace.re
  have h (p : BondInteriorCell L τ (normalFace τ)) :
      f (bondReflectCell τ (normalFace τ) p.val) =
        (periodicHolonomy (reflectPeriodic τ (-1) U) p.val.1 p.val.2).val.trace.re := by
    rw [← reflectFaceIndex_bond]
    exact (periodicHolonomy_reflect_re τ (-1) U p.val.1 p.val.2).symm
  unfold periodicLogWeight bondSeamAction bondInteriorAction
  change (N : ℝ) * β * (∑ p, f p) = _
  rw [← e.sum_comp f, Fintype.sum_sum_type, Fintype.sum_sum_type]
  change (N : ℝ) * β * ((∑ p : SeamCell L τ (normalFace τ), f p.val) +
    ((∑ p : BondInteriorCell L τ (normalFace τ), f p.val) +
      (∑ p : BondInteriorCell L τ (normalFace τ), f (bondReflectCell τ (normalFace τ) p.val)))) = _
  simp only [h, f]
  ring

private theorem bondSeamFace_weight {L N : ℕ} [NeZero L] (τ : Axis) (β : ℝ) (U : TorusConfig L N)
    (hU : ∀ p ∈ bondSeamLinks L τ, U p = 1) (p : Face × TorusSite L)
    (hp : bondCutBoundary τ (normalFace τ) p) :
    Real.exp ((N : ℝ) * β * (periodicHolonomy U p.1 p.2).val.trace.re) =
      fundamentalKernel β (U (bondTangentAxis τ p.1, p.2))
        (U (bondTangentAxis τ p.1, p.2 + torusStep L τ)) := by
  obtain ⟨I, x⟩ := p
  have hn := (normalFace_true_iff τ I).mp hp.1
  have hseams := bondSeamFace_normal_links τ (I, x) hp
  have h₀ : U (τ, x) = 1 := hU _ hseams.1
  have h₁ : U (τ, x + torusStep L (bondTangentAxis τ I)) = 1 := hU _ hseams.2
  change Real.exp ((N : ℝ) * β * (U (I.axes.1, x) * U (I.axes.2, x + torusStep L I.axes.1) *
    (U (I.axes.1, x + torusStep L I.axes.2))⁻¹ * (U (I.axes.2, x))⁻¹).val.trace.re) = _
  by_cases h : I.axes.1 = τ
  · have hj : I.axes.2 = bondTangentAxis τ I := by simp [bondTangentAxis, h]
    rw [h, hj, h₀, h₁, one_mul, inv_one, mul_one]
    exact fundamentalKernel_symm β _ _
  · have hi : I.axes.1 = bondTangentAxis τ I := by simp [bondTangentAxis, h]
    rw [hn.resolve_left h, hi, h₀, h₁, mul_one, inv_one, mul_one]
    rfl

private def bondSeamRead {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis) (a : BondHalf L N τ)
    (p : SeamCell L τ (normalFace τ)) : UnitaryMatrix N :=
  a (bondSeamPositiveLink hL τ p.val p.property)

private def bondSeamKernel {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis) (β : ℝ)
    (a b : BondHalf L N τ) : ℝ :=
  averagedWilsonSlice (unitaryHaar N) β Finset.univ ∅ (bondSeamRead hL τ a) (bondSeamRead hL τ b)

private theorem bondSeamKernel_positive {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis) {β : ℝ} (hβ : 0 ≤ β) :
    PositiveKernel (bondSeamKernel (N := N) hL τ β) := by
  intro m v
  exact (averagedWilsonSlice_positive_order (unitaryHaar N) β hβ
    (Finset.univ : Finset (SeamCell L τ (normalFace τ))) ∅).1 m
    (fun i => bondSeamRead hL τ (v i))

set_option maxHeartbeats 800000 in
private theorem continuous_bondSeamKernel {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis) (β : ℝ) :
    Continuous (fun q : BondHalf L N τ × BondHalf L N τ => bondSeamKernel hL τ β q.1 q.2) := by
  simp only [bondSeamKernel, averagedWilsonSlice, Finset.notMem_empty, ite_false]
  apply continuous_finsetProd
  intro p _
  let j := bondSeamPositiveLink hL τ p.val p.property
  let X := BondHalf L N τ
  let f (q : X × X) : UnitaryMatrix N × UnitaryMatrix N := (q.1 j, q.2 j)
  have hf : Continuous f :=
    (((continuous_apply j).comp continuous_fst : Continuous (fun q : X × X => q.1 j))).prodMk
      ((continuous_apply j).comp continuous_snd : Continuous (fun q : X × X => q.2 j))
  change Continuous ((fun p : UnitaryMatrix N × UnitaryMatrix N => fundamentalKernel β p.1 p.2) ∘ f)
  exact (continuous_fundamentalKernel β).comp hf

private theorem bondSeamAction_eq_kernel {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L)
    (τ : Axis) (β : ℝ) (q : BondHalf L N τ × BondHalf L N τ) :
    Real.exp (bondSeamAction τ β (bondAssembly hL he τ q)) = bondSeamKernel hL τ β q.1 q.2 := by
  classical
  let U := bondAssembly hL he τ q
  have hU : ∀ p ∈ bondSeamLinks L τ, U p = 1 := fun p hp =>
    bondAssembly_seam hL he τ q ⟨p, (mem_bondSeamLinks τ p).mp hp⟩
  simp only [bondSeamAction, Finset.mul_sum, Real.exp_sum, bondSeamKernel, averagedWilsonSlice,
    Finset.notMem_empty, ite_false]
  apply Finset.prod_congr rfl
  intro p _
  rw [bondSeamFace_weight τ β U hU p.val p.property]
  let w := bondSeamPositiveLink hL τ p.val p.property
  let a : TorusLink L := (bondTangentAxis τ p.val.1, p.val.2)
  let b : TorusLink L := (bondTangentAxis τ p.val.1, p.val.2 + torusStep L τ)
  let r := bondReflectCell (L := L) τ (normalLink τ)
  have hr : r a = b := bondSeamFace_tangents_reflect hL he τ p.val p.property
  have hr' : r b = a := hr ▸ bondReflectCell_involutive τ (normalLink τ) a
  have hn : ¬ normalLink τ w.val.1 := by
    change ¬ normalLink τ (bondTangentAxis τ p.val.1) = true
    exact fun h => bondTangentAxis_ne τ p.val.1 ((normalLink_true_iff τ _).mp h)
  have h₀ : U w.val = q.1 w := bondAssembly_positive hL he τ q w
  have h₁ : U (r w.val) = q.2 w := by
    simpa only [ite_eq_right hn] using bondAssembly_negative hL he τ q w
  change fundamentalKernel β (U a) (U b) = fundamentalKernel β (q.1 w) (q.2 w)
  by_cases ht : (p.val.2 τ).val < L / 2
  · have hw : w.val = a := by simp [w, a, bondSeamPositiveLink, ht]
    rw [hw, hr] at h₁
    rw [hw] at h₀
    rw [h₀, h₁]
  · have hw : w.val = b := by simp [w, b, bondSeamPositiveLink, ht]
    rw [hw, hr'] at h₁
    rw [hw] at h₀
    rw [h₀, h₁, fundamentalKernel_symm]

/-- The fundamental Wilson probability on an even torus is bond reflection
positive on continuous gauge-invariant observables of the strict half. -/
theorem periodicWilson_bondReflection_nonneg {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (heven : Even L)
    (τ : Axis) (β : ℝ) (hβ : 0 ≤ β) (f : TorusConfig L N → ℝ) (hf : Continuous f)
    (hg : PeriodicGaugeInvariant f)
    (hs : ∀ U V, (∀ p, bondCutInterior τ (normalLink τ) p → U p = V p) → f U = f V) :
    0 ≤ ∫ U, f (reflectPeriodic τ (-1) U) * f U ∂periodicWilson L N β := by
  have he : 2 * (L / 2) = L := by obtain ⟨k, hk⟩ := heven; omega
  let X := BondHalf L N τ
  let U := bondAssembly (N := N) hL he τ
  let F (v : TorusConfig L N) := Real.exp (periodicLogWeight β v) * (f (reflectPeriodic τ (-1) v) * f v)
  have hF : Continuous F :=
    (Real.continuous_exp.comp (continuous_periodicLogWeight β)).mul
      ((hf.comp (continuous_reflectPeriodic τ (-1))).mul hf)
  have hFg : PeriodicGaugeInvariant F := fun g v => by
    simp only [F, periodicLogWeight_gauge, periodicGauge_reflect]
    rw [hg (g ∘ reflectSiteOn τ (-1)) (reflectPeriodic τ (-1) v), hg g v]
  rw [integral_periodicWilson_eq]
  apply mul_nonneg ENNReal.toReal_nonneg
  change 0 ≤ ∫ v, F v ∂periodicHaar L N
  rw [integral_periodicHaar_gaugeFix (bondSeamLinks L τ) (bondSeamGauge τ) (bondSeamGauge_fixes hL τ) F hF hFg,
    integral_exterior_bondAssembly hL he τ F hF.measurable]
  let rep (a : X) := U (a, 1)
  let A (a : X) := Real.exp (bondInteriorAction τ β (rep a)) * f (rep a)
  let K := bondSeamKernel (N := N) hL τ β
  have hr : Continuous rep := (continuous_bondAssembly hL he τ).comp (continuous_id.prodMk continuous_const)
  have hA : Continuous A :=
    (Real.continuous_exp.comp ((continuous_bondInteriorAction τ β).comp hr)).mul (hf.comp hr)
  have hrep (q : X × X) (p : TorusLink L) (hp : bondCutInterior τ (normalLink τ) p) :
      U q p = rep q.1 p :=
    (bondAssembly_positive hL he τ q ⟨p, hp⟩).trans
      (bondAssembly_positive hL he τ (q.1, 1) ⟨p, hp⟩).symm
  have hi (q : X × X) : bondInteriorAction τ β (U q) = bondInteriorAction τ β (rep q.1) := by
    unfold bondInteriorAction
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [periodicHolonomy_congr p.val fun e he => hrep q e
      (bondPositivePlaquette_links hL τ p.val p.property e he)]
  have heq (q : X × X) : F (U q) = weightedKernel A K q.1 q.2 := by
    change Real.exp (periodicLogWeight β (U q)) * (f (reflectPeriodic τ (-1) (U q)) * f (U q)) = _
    rw [bondCut_action_split hL he τ β,
      show reflectPeriodic τ (-1) (U q) = U (q.2, q.1) from bondAssembly_reflect hL he τ q,
      hi q, hi (q.2, q.1), hs _ _ (hrep q), hs _ _ (hrep (q.2, q.1)), Real.exp_add, Real.exp_add]
    rw [show Real.exp (bondSeamAction τ β (U q)) = K q.1 q.2 from bondSeamAction_eq_kernel hL he τ β q]
    simp only [weightedKernel, A]
    ring
  change 0 ≤ ∫ q, F (U q) ∂(bondHalfHaar τ).prod (bondHalfHaar τ)
  simp_rw [heq]
  exact ((bondSeamKernel_positive hL τ hβ).weighted A).integral_nonneg
    (continuous_weightedKernel hA (continuous_bondSeamKernel hL τ β)) (bondHalfHaar τ)

end

end GaplessYangMills
