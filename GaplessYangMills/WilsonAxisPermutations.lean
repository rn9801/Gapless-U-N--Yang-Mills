module

public import GaplessYangMills.WilsonReflections
public import Mathlib.Tactic.FinCases

/-!
# Permutation of coordinate directions

Relabeling the axes permutes the independent Haar links and the geometric
plaquettes. Reordering a plaquette's axes inverts its ordered holonomy,
so the real trace and the Wilson law are invariant.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped Topology

def permuteSite {A : Type*} (σ : Equiv.Perm Axis) (x : Axis → A) : Axis → A :=
  x ∘ σ.symm

theorem permuteSite_symm {A : Type*} (σ : Equiv.Perm Axis) (x : Axis → A) :
    permuteSite σ.symm (permuteSite σ x) = x := by
  funext i
  simp [permuteSite]

def permuteSiteEquiv (A : Type*) (σ : Equiv.Perm Axis) : (Axis → A) ≃ (Axis → A) where
  toFun := permuteSite σ
  invFun := permuteSite σ.symm
  left_inv := permuteSite_symm σ
  right_inv x := by simpa only [Equiv.symm_symm] using permuteSite_symm σ.symm x

theorem permuteSite_add {A : Type*} [Add A] (σ : Equiv.Perm Axis) (x y : Axis → A) :
    permuteSite σ (x + y) = permuteSite σ x + permuteSite σ y := rfl

theorem permuteSite_torusStep (L : ℕ) (σ : Equiv.Perm Axis) (i : Axis) :
    permuteSite σ (torusStep L i) = torusStep L (σ i) := by
  funext j
  have h : i = σ.symm j ↔ σ i = j := by
    rw [← σ.apply_eq_iff_eq, σ.apply_symm_apply]
  simp [permuteSite, torusStep, h]

theorem permuteSite_step (σ : Equiv.Perm Axis) (i : Axis) :
    permuteSite σ (step i) = step (σ i) := by
  funext j
  have h : i = σ.symm j ↔ σ i = j := by
    rw [← σ.apply_eq_iff_eq, σ.apply_symm_apply]
  simp [permuteSite, step, h]

def faceBetween (i j : Axis) : Face :=
  match min i.val j.val, max i.val j.val with
  | 0, 1 => .xy
  | 0, 2 => .xz
  | 0, 3 => .xw
  | 1, 2 => .yz
  | 1, 3 => .yw
  | _, _ => .zw

private theorem faceBetween_axes (i j : Axis) :
    i ≠ j → (faceBetween i j).axes = (i, j) ∨ (faceBetween i j).axes = (j, i) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem face_eq_of_axes_eq_or_swap (I J : Face) :
    I.axes = (J.axes.1, J.axes.2) ∨ I.axes = (J.axes.2, J.axes.1) → I = J := by
  cases I <;> cases J <;> decide

def permuteFace (σ : Equiv.Perm Axis) (I : Face) : Face :=
  faceBetween (σ I.axes.1) (σ I.axes.2)

theorem permuteFace_axes (σ : Equiv.Perm Axis) (I : Face) :
    (permuteFace σ I).axes = (σ I.axes.1, σ I.axes.2) ∨
      (permuteFace σ I).axes = (σ I.axes.2, σ I.axes.1) := by
  have h : I.axes.1 ≠ I.axes.2 := by cases I <;> decide
  exact faceBetween_axes (σ I.axes.1) (σ I.axes.2) (σ.injective.ne h)

theorem permuteFace_symm (σ : Equiv.Perm Axis) (I : Face) :
    permuteFace σ.symm (permuteFace σ I) = I := by
  have h := permuteFace_axes σ.symm (permuteFace σ I)
  apply face_eq_of_axes_eq_or_swap
  rcases permuteFace_axes σ I with h₁ | h₁
  · rw [h₁] at h
    simpa only [Equiv.symm_apply_apply] using h
  · rw [h₁] at h
    simpa only [Equiv.symm_apply_apply, or_comm] using h

def permuteFaceEquiv (σ : Equiv.Perm Axis) : Face ≃ Face where
  toFun := permuteFace σ
  invFun := permuteFace σ.symm
  left_inv := permuteFace_symm σ
  right_inv I := by simpa only [Equiv.symm_symm] using permuteFace_symm σ.symm I

def permuteConfig {N : ℕ} (σ : Equiv.Perm Axis) (U : InfiniteConfig N) : InfiniteConfig N :=
  fun e => U (σ e.1, permuteSite σ e.2)

def permutePeriodic {L N : ℕ} (σ : Equiv.Perm Axis) (U : TorusConfig L N) : TorusConfig L N :=
  fun e => U (σ e.1, permuteSite σ e.2)

theorem continuous_permuteConfig {N : ℕ} (σ : Equiv.Perm Axis) :
    Continuous (permuteConfig σ : InfiniteConfig N → InfiniteConfig N) :=
  continuous_pi fun e => continuous_apply (σ e.1, permuteSite σ e.2)

theorem permuteConfig_symm {N : ℕ} (σ : Equiv.Perm Axis) (U : InfiniteConfig N) :
    permuteConfig σ.symm (permuteConfig σ U) = U := by
  funext p
  obtain ⟨i, x⟩ := p
  have h := permuteSite_symm σ.symm x
  simpa only [permuteConfig, σ.apply_symm_apply, Equiv.symm_symm] using congrArg (fun y => U (i, y)) h

theorem translateConfig_permuteConfig {N : ℕ} (σ : Equiv.Perm Axis) (a : Site) (U : InfiniteConfig N) :
    translateConfig a (permuteConfig σ U) = permuteConfig σ (translateConfig (permuteSite σ a) U) := by
  funext p
  obtain ⟨i, x⟩ := p
  simp only [translateConfig, permuteConfig, permuteSite_add]

theorem reflectSiteOn_permuteSite {A : Type*} [Sub A] (σ : Equiv.Perm Axis)
    (τ : Axis) (c : A) (x : Axis → A) :
    permuteSite σ (reflectSiteOn τ c x) = reflectSiteOn (σ τ) c (permuteSite σ x) := by
  funext j
  have h : σ.symm j = τ ↔ j = σ τ := by rw [← σ.apply_eq_iff_eq, σ.apply_symm_apply]
  simp [permuteSite, reflectSiteOn, h]

theorem reflectConfig_permuteConfig {N : ℕ} (σ : Equiv.Perm Axis) (τ : Axis) (c : ℤ) (U : InfiniteConfig N) :
    reflectConfig τ c (permuteConfig σ U) = permuteConfig σ (reflectConfig (σ τ) c U) := by
  funext p
  obtain ⟨i, x⟩ := p
  by_cases hi : i = τ
  · subst i
    simp only [reflectConfig, reflectLinksOn_normal, permuteConfig, reflectSiteOn_permuteSite]
  · simp only [reflectConfig, reflectLinksOn_tangent hi, reflectLinksOn_tangent (σ.injective.ne hi),
      permuteConfig, reflectSiteOn_permuteSite]

private theorem periodicHolonomy_permute_re {L N : ℕ} (σ : Equiv.Perm Axis)
    (U : TorusConfig L N) (I : Face) (x : TorusSite L) :
    (periodicHolonomy (permutePeriodic σ U) I x).val.trace.re =
      (periodicHolonomy U (permuteFace σ I) (permuteSite σ x)).val.trace.re := by
  let y := permuteSite σ x
  let i := σ I.axes.1
  let j := σ I.axes.2
  let P (a b : Axis) := U (a, y) * U (b, y + torusStep L a) *
    (U (a, y + torusStep L b))⁻¹ * (U (b, y))⁻¹
  have hL : periodicHolonomy (permutePeriodic σ U) I x = P i j := by
    simp only [periodicHolonomy, permutePeriodic, permuteSite_add, permuteSite_torusStep, P, i, j, y]
  rw [hL]
  have hR : periodicHolonomy U (permuteFace σ I) y = P i j ∨
      periodicHolonomy U (permuteFace σ I) y = (P i j)⁻¹ := by
    rcases permuteFace_axes σ I with h | h
    · left
      simp only [periodicHolonomy, h, P, i, j]
    · right
      simp only [periodicHolonomy, h, P, i, j]
      group
  rcases hR with h | h
  · rw [h]
  · rw [h, unitaryTrace_re_inv]

theorem periodicLogWeight_permute {L N : ℕ} [NeZero L] (β : ℝ) (σ : Equiv.Perm Axis)
    (U : TorusConfig L N) : periodicLogWeight β (permutePeriodic σ U) = periodicLogWeight β U := by
  simp only [periodicLogWeight, periodicHolonomy_permute_re]
  congr 1
  let e := Equiv.prodCongr (permuteFaceEquiv σ) (permuteSiteEquiv (ZMod L) σ)
  exact e.sum_comp fun p => (periodicHolonomy U p.1 p.2).val.trace.re

theorem periodicHaar_permute_preserving {L N : ℕ} [NeZero L] (σ : Equiv.Perm Axis) :
    MeasurePreserving (permutePeriodic σ : TorusConfig L N → TorusConfig L N)
      (periodicHaar L N) (periodicHaar L N) := by
  let e : TorusLink L ≃ TorusLink L := Equiv.prodCongr σ (permuteSiteEquiv (ZMod L) σ)
  have h : ⇑(MeasurableEquiv.piCongrLeft (fun _ : TorusLink L => UnitaryMatrix N) e.symm) =
      (permutePeriodic σ : TorusConfig L N → TorusConfig L N) := by
    funext U p
    change (MeasurableEquiv.piCongrLeft (fun _ : TorusLink L => UnitaryMatrix N) e.symm) U p = U (e p)
    simpa only [Equiv.symm_apply_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : TorusLink L => UnitaryMatrix N) e.symm U (e p))
  rw [← h]
  exact measurePreserving_piCongrLeft (fun _ : TorusLink L => unitaryHaar N) e.symm

theorem periodicWilson_permute_preserving {L N : ℕ} [NeZero L] (β : ℝ) (σ : Equiv.Perm Axis) :
    MeasurePreserving (permutePeriodic σ : TorusConfig L N → TorusConfig L N)
      (periodicWilson L N β) (periodicWilson L N β) :=
  periodicWilson_preserving_of_logWeight β _ (periodicHaar_permute_preserving σ) (periodicLogWeight_permute β σ)

theorem extendedWilson_permute {L N : ℕ} [NeZero L] (β : ℝ) (σ : Equiv.Perm Axis) :
    ProbabilityMeasure.map (extendedWilson L N β) (permuteConfig σ) = extendedWilson L N β := by
  apply Subtype.ext
  change Measure.map (permuteConfig σ) (Measure.map extendPeriodic (periodicWilson L N β)) =
    Measure.map extendPeriodic (periodicWilson L N β)
  have he := (continuous_extendPeriodic L N).measurable
  have hp := periodicWilson_permute_preserving (L := L) (N := N) β σ
  have hf : (permuteConfig σ : InfiniteConfig N → InfiniteConfig N) ∘ extendPeriodic =
      extendPeriodic ∘ permutePeriodic (L := L) σ := rfl
  rw [Measure.map_map (continuous_permuteConfig σ).measurable he, hf,
    ← Measure.map_map he hp.measurable, hp.map_eq]

theorem periodicWilson_limit_permute {N : ℕ} (β : ℝ) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) : ProbabilityMeasure.map μ (permuteConfig σ) = μ := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ (continuous_permuteConfig σ)
  simp only [extendedWilson_permute] at h
  exact tendsto_nhds_unique h hμ

end GaplessYangMills
