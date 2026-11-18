module

public import GaplessYangMills.FiniteGibbs
public import GaplessYangMills.ReflectionProduct
public import GaplessYangMills.SiteReflectionGeometry
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Site reflection positivity of the periodic Wilson measure

Conditioning on both separating planes leaves two independent Haar halves.
The Wilson density separates between the two halves and the planes. The
reflected observable therefore integrates to a nonnegative square.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal Topology

noncomputable section

theorem integral_periodicWilson_eq {L N : ℕ} [NeZero L] (β : ℝ) (f : TorusConfig L N → ℝ) :
    (∫ U, f U ∂periodicWilson L N β) =
      ((periodicPartition L N β)⁻¹).toReal *
        ∫ U, Real.exp (periodicLogWeight β U) * f U ∂periodicHaar L N := by
  rw [periodicWilson, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (periodicWeight_measurable β)
      (ae_of_all _ fun U => ENNReal.ofReal_lt_top) f]
  simp only [smul_eq_mul, periodicWeight, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

private theorem normalFace_false {τ : Axis} {I : Face} (h : normalFace τ I = false) :
    I.axes.1 ≠ τ ∧ I.axes.2 ≠ τ := by
  simpa only [normalFace, decide_eq_false_iff_not, not_or] using h

private theorem siteBoundaryPlaquette_links {L : ℕ} [NeZero L] (τ : Axis)
    (p : Face × TorusSite L) (hp : siteCutBoundary τ (normalFace τ) p) :
    ∀ e ∈ periodicBoundaryLinks p, siteCutBoundary τ (normalLink τ) e := by
  obtain ⟨I, x⟩ := p
  obtain ⟨hn, ht⟩ := hp
  have hi := (normalFace_false hn).1
  have hj := (normalFace_false hn).2
  intro e he
  simp only [periodicBoundaryLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨by simp [normalLink, hi], ht⟩
  · exact ⟨by simp [normalLink, hj], by simpa only [torusStep_time_eq, ite_eq_right hi] using ht⟩
  · exact ⟨by simp [normalLink, hi], by simpa only [torusStep_time_eq, ite_eq_right hj] using ht⟩
  · exact ⟨by simp [normalLink, hj], ht⟩

private theorem sitePositivePlaquette_links {L : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis)
    (p : Face × TorusSite L) (hp : siteCutPositive τ (normalFace τ) p) :
    ∀ e ∈ periodicBoundaryLinks p, siteCutPositive τ (normalLink τ) e := by
  have hh : 0 < L / 2 := by omega
  rcases hp with hb | hi
  · exact fun e he => Or.inl (siteBoundaryPlaquette_links τ p hb e he)
  obtain ⟨I, x⟩ := p
  have hlt : (x τ).val < L / 2 := hi.1
  have hshift (i j : Axis) (hij : i ≠ j) :
      siteCutPositive τ (normalLink τ) (i, x + torusStep L j) := by
    apply (siteCutPositive_iff τ _ _ hh).mpr
    change ((x + torusStep L j) τ).val < L / 2 ∨
      (normalLink τ i = false ∧ ((x + torusStep L j) τ).val = L / 2)
    by_cases hj : j = τ
    · have hi : i ≠ τ := fun h => hij (h.trans hj.symm)
      rw [torusStep_time_eq, ite_eq_left hj, ZMod.val_add, ZMod.val_one'' (by omega : L ≠ 1),
        Nat.mod_eq_of_lt (by omega)]
      by_cases he : (x τ).val + 1 = L / 2
      · exact Or.inr ⟨by simp [normalLink, hi], he⟩
      · exact Or.inl (by omega)
    · rw [torusStep_time_eq, ite_eq_right hj]
      exact Or.inl hlt
  have hbase (i : Axis) : siteCutPositive τ (normalLink τ) (i, x) :=
    (siteCutPositive_iff τ _ _ hh).mpr (Or.inl hlt)
  have hne : I.axes.1 ≠ I.axes.2 := by cases I <;> decide
  intro e he
  simp only [periodicBoundaryLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hbase I.axes.1
  · exact hshift I.axes.2 I.axes.1 hne.symm
  · exact hshift I.axes.1 I.axes.2 hne
  · exact hbase I.axes.2

private abbrev BoundaryCell (L : ℕ) {J : Type*} (τ : Axis) (normal : J → Bool) :=
  {p // siteCutBoundary (L := L) τ normal p}

private abbrev InteriorCell (L : ℕ) {J : Type*} (τ : Axis) (normal : J → Bool) :=
  {p // siteCutInterior (L := L) τ normal p}

attribute [local instance] Fintype.ofFinite

private def boundaryAction {L N : ℕ} [NeZero L] (τ : Axis) (β : ℝ) (U : TorusConfig L N) : ℝ :=
  (N : ℝ) * β * ∑ p : BoundaryCell L τ (normalFace τ), (periodicHolonomy U p.val.1 p.val.2).val.trace.re

private def interiorAction {L N : ℕ} [NeZero L] (τ : Axis) (β : ℝ) (U : TorusConfig L N) : ℝ :=
  (N : ℝ) * β * ∑ p : InteriorCell L τ (normalFace τ), (periodicHolonomy U p.val.1 p.val.2).val.trace.re

private theorem continuous_boundaryAction {L N : ℕ} [NeZero L] (τ : Axis) (β : ℝ) :
    Continuous (boundaryAction τ β : TorusConfig L N → ℝ) := by
  unfold boundaryAction
  apply continuous_const.mul
  exact continuous_finsetSum _ fun p _ => Complex.continuous_re.comp
    (Continuous.matrix_trace (continuous_subtype_val.comp (continuous_periodicHolonomy p.val.1 p.val.2)))

private theorem continuous_interiorAction {L N : ℕ} [NeZero L] (τ : Axis) (β : ℝ) :
    Continuous (interiorAction τ β : TorusConfig L N → ℝ) := by
  unfold interiorAction
  apply continuous_const.mul
  exact continuous_finsetSum _ fun p _ => Complex.continuous_re.comp
    (Continuous.matrix_trace (continuous_subtype_val.comp (continuous_periodicHolonomy p.val.1 p.val.2)))

private theorem siteCut_action_split {L N : ℕ} [NeZero L] (hL : 2 * (L / 2) = L)
    (τ : Axis) (β : ℝ) (U : TorusConfig L N) :
    periodicLogWeight β U = boundaryAction τ β U +
      interiorAction τ β U + interiorAction τ β (reflectPeriodic τ 0 U) := by
  let e := siteCutCellEquiv hL τ (normalFace τ)
  let f (p : Face × TorusSite L) := (periodicHolonomy U p.1 p.2).val.trace.re
  have h (p : InteriorCell L τ (normalFace τ)) :
      f (siteReflectCell τ (normalFace τ) p.val) =
        (periodicHolonomy (reflectPeriodic τ 0 U) p.val.1 p.val.2).val.trace.re := by
    rw [← reflectFaceIndex_site]
    exact (periodicHolonomy_reflect_re τ 0 U p.val.1 p.val.2).symm
  unfold periodicLogWeight boundaryAction interiorAction
  change (N : ℝ) * β * (∑ p, f p) = _
  rw [← e.sum_comp f, Fintype.sum_sum_type, Fintype.sum_sum_type]
  change (N : ℝ) * β * ((∑ p : BoundaryCell L τ (normalFace τ), f p.val) +
    ((∑ p : InteriorCell L τ (normalFace τ), f p.val) +
      (∑ p : InteriorCell L τ (normalFace τ), f (siteReflectCell τ (normalFace τ) p.val)))) = _
  simp only [h, f]
  ring

private abbrev SiteCutCoords (L N : ℕ) (τ : Axis) :=
  (BoundaryCell L τ (normalLink τ) → UnitaryMatrix N) ×
    ((InteriorCell L τ (normalLink τ) → UnitaryMatrix N) ×
      (InteriorCell L τ (normalLink τ) → UnitaryMatrix N))

private def siteCutAssembly {L N : ℕ} [NeZero L] (hL : 2 * (L / 2) = L) (τ : Axis) :
    SiteCutCoords L N τ → TorusConfig L N :=
  assembleReflection (siteCutCellEquiv hL τ (normalLink τ)) (fun p => normalLink τ p.val.1)

private theorem siteCutAssembly_boundary {L N : ℕ} [NeZero L] (hL : 2 * (L / 2) = L) (τ : Axis)
    (q : SiteCutCoords L N τ) (p : BoundaryCell L τ (normalLink τ)) :
    siteCutAssembly hL τ q p.val = q.1 p :=
  assembleReflection_boundary (siteCutCellEquiv hL τ (normalLink τ)) _ _ _

private theorem siteCutAssembly_positive {L N : ℕ} [NeZero L] (hL : 2 * (L / 2) = L) (τ : Axis)
    (q : SiteCutCoords L N τ) (p : InteriorCell L τ (normalLink τ)) :
    siteCutAssembly hL τ q p.val = q.2.1 p :=
  assembleReflection_positive (siteCutCellEquiv hL τ (normalLink τ)) _ _ _

private theorem siteCutAssembly_negative {L N : ℕ} [NeZero L] (hL : 2 * (L / 2) = L) (τ : Axis)
    (q : SiteCutCoords L N τ) (p : InteriorCell L τ (normalLink τ)) :
    siteCutAssembly hL τ q (siteReflectCell τ (normalLink τ) p.val) =
      if normalLink τ p.val.1 then (q.2.2 p)⁻¹ else q.2.2 p :=
  assembleReflection_negative (siteCutCellEquiv hL τ (normalLink τ)) _ _ _

private theorem siteCutAssembly_reflect {L N : ℕ} [NeZero L] (hL : 2 * (L / 2) = L) (τ : Axis)
    (q : SiteCutCoords L N τ) :
    reflectPeriodic τ 0 (siteCutAssembly hL τ q) = siteCutAssembly hL τ (q.1, q.2.2, q.2.1) := by
  let r := siteReflectCell (L := L) τ (normalLink τ)
  have hrefl (U : TorusConfig L N) (p : TorusLink L) :
      reflectPeriodic τ 0 U p = if normalLink τ p.1 then (U (r p))⁻¹ else U (r p) := by
    by_cases h : p.1 = τ <;> simp [reflectPeriodic, reflectLinksOn, normalLink, h, r, reflectLinkIndex_site]
  funext p
  obtain ⟨v, rfl⟩ := (siteCutCellEquiv hL τ (normalLink τ)).surjective p
  rcases v with b | p | p
  · change reflectPeriodic τ 0 (siteCutAssembly hL τ q) b.val =
      siteCutAssembly hL τ (q.1, q.2.2, q.2.1) b.val
    rw [hrefl, show r b.val = b.val from siteReflectCell_boundary hL τ _ _ b.property,
      siteCutAssembly_boundary, siteCutAssembly_boundary]
    simp [b.property.1]
  · change reflectPeriodic τ 0 (siteCutAssembly hL τ q) p.val =
      siteCutAssembly hL τ (q.1, q.2.2, q.2.1) p.val
    rw [hrefl, show r p.val = siteReflectCell τ (normalLink τ) p.val from rfl,
      siteCutAssembly_negative, siteCutAssembly_positive]
    by_cases hn : normalLink τ p.val.1 <;> simp [hn]
  · change reflectPeriodic τ 0 (siteCutAssembly hL τ q) (r p.val) =
      siteCutAssembly hL τ (q.1, q.2.2, q.2.1) (siteReflectCell τ (normalLink τ) p.val)
    rw [hrefl, show r (r p.val) = p.val from siteReflectCell_involutive τ _ _,
      siteCutAssembly_positive, siteCutAssembly_negative]
    rfl

/-- Finite-volume site reflection positivity for continuous observables
whose links lie in the closed positive half, including both planes. -/
theorem periodicWilson_siteReflection_nonneg {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (heven : Even L)
    (τ : Axis) (β : ℝ) (f : TorusConfig L N → ℝ) (hf : Continuous f)
    (hs : ∀ U V, (∀ p, siteCutPositive τ (normalLink τ) p → U p = V p) → f U = f V) :
    0 ≤ ∫ U, f (reflectPeriodic τ 0 U) * f U ∂periodicWilson L N β := by
  have hL' : 2 * (L / 2) = L := by obtain ⟨k, hk⟩ := heven; omega
  let X := InteriorCell L τ (normalLink τ) → UnitaryMatrix N
  let B := BoundaryCell L τ (normalLink τ) → UnitaryMatrix N
  let mX : Measure X := Measure.pi fun _ => unitaryHaar N
  let mB : Measure B := Measure.pi fun _ => unitaryHaar N
  let U := siteCutAssembly (N := N) hL' τ
  let rep (p : B × X) := U (p.1, p.2, 1)
  let w (b : B) := Real.exp (boundaryAction τ β (U (b, 1, 1)))
  let A (p : B × X) := Real.exp (interiorAction τ β (rep p)) * f (rep p)
  have hU : Continuous U := continuous_assembleReflection _ _
  have hm : MeasurePreserving U (mB.prod (mX.prod mX)) (periodicHaar L N) :=
    measurePreserving_assembleReflection _ _
  have hrep (q : SiteCutCoords L N τ) (p : TorusLink L) (hp : siteCutPositive τ (normalLink τ) p) :
      U q p = rep (q.1, q.2.1) p := by
    rcases hp with hb | hi
    · exact (siteCutAssembly_boundary hL' τ q ⟨p, hb⟩).trans
        (siteCutAssembly_boundary hL' τ (q.1, q.2.1, 1) ⟨p, hb⟩).symm
    · exact (siteCutAssembly_positive hL' τ q ⟨p, hi⟩).trans
        (siteCutAssembly_positive hL' τ (q.1, q.2.1, 1) ⟨p, hi⟩).symm
  have hb (q : SiteCutCoords L N τ) : boundaryAction τ β (U q) = boundaryAction τ β (U (q.1, 1, 1)) := by
    unfold boundaryAction
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [periodicHolonomy_congr p.val fun e he =>
      (siteCutAssembly_boundary hL' τ q ⟨e, siteBoundaryPlaquette_links τ p.val p.property e he⟩).trans
        (siteCutAssembly_boundary hL' τ (q.1, 1, 1)
          ⟨e, siteBoundaryPlaquette_links τ p.val p.property e he⟩).symm]
  have hi (q : SiteCutCoords L N τ) :
      interiorAction τ β (U q) = interiorAction τ β (rep (q.1, q.2.1)) := by
    unfold interiorAction
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [periodicHolonomy_congr p.val fun e he => hrep q e
      (sitePositivePlaquette_links hL τ p.val (Or.inr p.property) e he)]
  rw [integral_periodicWilson_eq]
  apply mul_nonneg ENNReal.toReal_nonneg
  have hg : Continuous (fun v : TorusConfig L N =>
      Real.exp (periodicLogWeight β v) * (f (reflectPeriodic τ 0 v) * f v)) :=
    (Real.continuous_exp.comp (continuous_periodicLogWeight β)).mul
      ((hf.comp (continuous_reflectPeriodic τ 0)).mul hf)
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hg.measurable.aestronglyMeasurable]
  have hsplit (q : SiteCutCoords L N τ) :
      Real.exp (periodicLogWeight β (U q)) * (f (reflectPeriodic τ 0 (U q)) * f (U q)) =
        w q.1 * (A (q.1, q.2.1) * A (q.1, q.2.2)) := by
    rw [siteCut_action_split hL' τ β, show reflectPeriodic τ 0 (U q) = U (q.1, q.2.2, q.2.1)
      from siteCutAssembly_reflect hL' τ q, hb q, hi q, hi (q.1, q.2.2, q.2.1),
      hs _ _ (hrep q), hs _ _ (hrep (q.1, q.2.2, q.2.1)), Real.exp_add, Real.exp_add]
    dsimp only [w, A]
    ring
  have hw : Continuous w := Real.continuous_exp.comp ((continuous_boundaryAction τ β).comp
    (hU.comp (continuous_id.prodMk continuous_const)))
  have hr : Continuous rep := hU.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  have hA : Continuous A :=
    (Real.continuous_exp.comp ((continuous_interiorAction τ β).comp hr)).mul (hf.comp hr)
  change 0 ≤ ∫ q, Real.exp (periodicLogWeight β (U q)) * (f (reflectPeriodic τ 0 (U q)) * f (U q))
    ∂mB.prod (mX.prod mX)
  simp_rw [hsplit]
  exact integral_reflection_square_nonneg mB mX w hw (fun _ => Real.exp_nonneg _) A hA

/-- A finite-link observable with all lower endpoints at times at least `k`. -/
def HalfSpaceCylinder {N : ℕ} (τ : Axis) (k : ℤ) (f : InfiniteConfig N → ℝ) : Prop :=
  ∃ S : Finset (Axis × Site), (∀ e ∈ S, k ≤ e.2 τ) ∧
    ∀ U V, (∀ e ∈ S, U e = V e) → f U = f V

/-- Site reflection positivity passes to every periodic weak limit on
continuous positive-time cylinder observables. -/
theorem periodicLimit_siteReflection_nonneg {N : ℕ} (β : ℝ) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (f : InfiniteConfig N → ℝ) (hf : Continuous f)
    (hs : HalfSpaceCylinder τ 0 f) :
    0 ≤ ∫ U, f (reflectConfig τ 0 U) * f U ∂μ.toMeasure := by
  let g : InfiniteConfig N →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun U => f (reflectConfig τ 0 U) * f U, (hf.comp (continuous_reflectConfig τ 0)).mul hf⟩
  obtain ⟨S, ht, hsupport⟩ := hs
  let m := S.sup (fun e => (e.2 τ).toNat)
  have htend := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ g
  apply ge_of_tendsto htend
  filter_upwards [hl.tendsto_atTop.eventually_ge_atTop m] with n hn
  let L := evenLength (l n)
  let F (U : TorusConfig L N) := f (extendPeriodic U)
  have hL : 4 ≤ L := by unfold L evenLength; omega
  have hL' : Even L := ⟨l n + 2, by unfold L evenLength; omega⟩
  have hF : Continuous F := hf.comp (continuous_extendPeriodic L N)
  have hS : ∀ U V : TorusConfig L N, (∀ p, siteCutPositive τ (normalLink τ) p → U p = V p) →
      F U = F V := by
    intro U V huv
    apply hsupport
    intro e he
    obtain ⟨i, x⟩ := e
    let y : TorusSite L := fun j => (x j : ZMod L)
    change U (i, y) = V (i, y)
    apply huv
    apply (siteCutPositive_iff τ (normalLink τ) (i, y) (by omega)).mpr
    left
    have hx : (x τ).toNat ≤ m := Finset.le_sup (f := fun e => (e.2 τ).toNat) he
    have hlen : m < L / 2 := by unfold L evenLength; omega
    have heq : (x τ : ZMod L) = ((x τ).toNat : ZMod L) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (ht (i, x) he)]
    change (x τ : ZMod L).val < L / 2
    rw [heq, ZMod.val_natCast_of_lt (by omega)]
    exact hx.trans_lt hlen
  change 0 ≤ ∫ U, g U ∂Measure.map extendPeriodic (periodicWilson L N β)
  rw [integral_map (continuous_extendPeriodic L N).measurable.aemeasurable
    g.continuous.measurable.aestronglyMeasurable]
  change 0 ≤ ∫ U : TorusConfig L N, f (reflectConfig τ 0 (extendPeriodic U)) * f (extendPeriodic U)
    ∂periodicWilson L N β
  simp_rw [reflectConfig_extendPeriodic, Int.cast_zero]
  exact periodicWilson_siteReflection_nonneg hL hL' τ β F hF hS

end

end GaplessYangMills
