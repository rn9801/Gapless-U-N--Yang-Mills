module

public import GaplessYangMills.WilsonCurrentSymmetries
public import GaplessYangMills.WilsonTransferCorrelations

/-!
# Time reflection and rotation of plaquette vectors

The current at the origin defines a positive-time vector in every
direction. When the current is placed on the negative side of the
reflection plane, its reflected vector is a signed time translate.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped Topology

noncomputable section

def wilsonCurrentHalfVector {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (τ : Axis) (J : Face) :
    wilsonHalfSpace μ τ :=
  ⟨wilsonCurrentL2 μ (J, 0), (wilsonCurrentObservable μ τ J).toL2_mem_halfSpace μ le_rfl⟩

def wilsonCurrentOSVector {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (J : Face) : (wilsonOSForm μ hl hμ τ).Hilbert :=
  (wilsonOSForm μ hl hμ τ).ofVector (wilsonCurrentHalfVector μ τ J)

def reflectedCurrentTime (τ : Axis) (J : Face) : ℕ :=
  if J.axes.1 = τ ∨ J.axes.2 = τ then 1 else 2

private theorem reflectedFaceBase_current (τ : Axis) (J : Face) :
    reflectedFaceBase τ (0 : ℤ) J ((-2 : ℤ) • step τ) = reflectedCurrentTime τ J • step τ := by
  funext i
  by_cases hi : i = τ
  · subst i
    by_cases hJ : J.axes.1 = τ ∨ J.axes.2 = τ <;>
      simp [reflectedFaceBase, reflectSiteOn, reflectedCurrentTime, step, hJ]
  · have h' : τ ≠ i := Ne.symm hi
    simp [reflectedFaceBase, reflectSiteOn, step, hi, h']

theorem wilsonCurrentL2_reflect {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (J : Face) :
    wilsonReflectL2 μ hμ τ 0 (wilsonTranslateL2 μ hμ ((-2 : ℤ) • step τ) (wilsonCurrentL2 μ (J, 0))) =
      plaquetteReflectionSign τ J •
        wilsonTranslateL2 μ hμ (reflectedCurrentTime τ J • step τ) (wilsonCurrentL2 μ (J, 0)) := by
  let F := wilsonCurrentObservable μ τ J
  let a : Site := (-2 : ℤ) • step τ
  let b : Site := reflectedCurrentTime τ J • step τ
  let G := (F.translate a).reflect 0
  let H := F.translate b
  let s := plaquetteReflectionSign τ J
  have hG : G.toL2 μ = wilsonReflectL2 μ hμ τ 0 (wilsonTranslateL2 μ hμ a (F.toL2 μ)) :=
    ((F.translate a).toL2_reflect μ hμ 0).trans (congrArg _ (F.toL2_translate μ hμ a))
  change wilsonReflectL2 μ hμ τ 0 (wilsonTranslateL2 μ hμ a (F.toL2 μ)) =
    s • wilsonTranslateL2 μ hμ b (F.toL2 μ)
  rw [← hG, ← F.toL2_translate μ hμ b]
  change G.toL2 μ = s • H.toL2 μ
  apply Lp.ext
  filter_upwards [G.toL2_ae μ, H.toL2_ae μ, Lp.coeFn_smul s (H.toL2 μ)] with U h₁ h₂ h₃
  rw [h₁, h₃]
  change centeredPlaquetteCurrent μ.toMeasure (translateConfig a (reflectConfig τ 0 U)) (J, 0) =
    s * H.toL2 μ U
  rw [h₂]
  change centeredPlaquetteCurrent μ.toMeasure (translateConfig a (reflectConfig τ 0 U)) (J, 0) =
    s * centeredPlaquetteCurrent μ.toMeasure (translateConfig b U) (J, 0)
  rw [centeredPlaquetteCurrent_translateConfig β μ hμ a, zero_add,
    centeredPlaquetteCurrent_reflectConfig μ hμ, reflectedFaceBase_current,
    centeredPlaquetteCurrent_translateConfig β μ hμ b, zero_add]

set_option maxHeartbeats 700000 in
theorem wilsonCurrentOSVector_reflect {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (J : Face) (u : wilsonHalfSpace μ τ)
    (hu : u.val = wilsonReflectL2 μ hμ τ 0
      (wilsonTranslateL2 μ hμ ((-2 : ℤ) • step τ) (wilsonCurrentL2 μ (J, 0)))) :
    (wilsonOSForm μ hl hμ τ).ofVector u =
      plaquetteReflectionSign τ J •
        (wilsonTransfer hβ μ hl hμ τ ^ reflectedCurrentTime τ J) (wilsonCurrentOSVector μ hl hμ τ J) := by
  let B := wilsonOSForm μ hl hμ τ
  let S := wilsonOSShift hβ μ hl hμ τ
  let v := wilsonCurrentHalfVector μ τ J
  let s := plaquetteReflectionSign τ J
  let k := reflectedCurrentTime τ J
  have he : u = s • ((wilsonInwardShift μ hμ τ ^ k) v) := by
    apply Subtype.ext
    change u.val = s • ((wilsonInwardShift μ hμ τ ^ k) v).val
    rw [hu, wilsonInwardShift_pow, wilsonCurrentL2_reflect]
    rfl
  change B.ofVector u = s • (S.transfer ^ k) (B.ofVector v)
  rw [he, PositiveReflectionForm.ofVector_smul, PositiveReflectionForm.Shift.transfer_pow_ofVector]
  rfl

theorem wilsonCurrentL2_permute {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (J : Face) :
    wilsonPermuteL2 μ hμ σ (wilsonCurrentL2 μ (J, 0)) =
      plaquettePermutationSign σ J • wilsonCurrentL2 μ (permuteFace σ J, 0) := by
  let F := wilsonCurrentObservable μ 0 J
  let G := wilsonCurrentObservable μ 0 (permuteFace σ J)
  let h := measurePreserving_permuteConfig μ hμ σ
  let s := plaquettePermutationSign σ J
  change Lp.compMeasurePreserving _ h (F.toL2 μ) = s • G.toL2 μ
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (F.toL2 μ) h,
    h.quasiMeasurePreserving.ae (F.toL2_ae μ), G.toL2_ae μ, Lp.coeFn_smul s (G.toL2 μ)] with U h₁ h₂ h₃ h₄
  rw [h₁, Function.comp_apply, h₂, h₄]
  change centeredPlaquetteCurrent μ.toMeasure (permuteConfig σ U) (J, 0) = s * G.toL2 μ U
  rw [h₃, centeredPlaquetteCurrent_permuteConfig μ hμ]
  rfl

theorem norm_wilsonCurrentL2_permute {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (J : Face) :
    ‖wilsonCurrentL2 μ (J, 0)‖ = ‖wilsonCurrentL2 μ (permuteFace σ J, 0)‖ := by
  rw [← (wilsonPermuteL2 μ hμ σ).norm_map, wilsonCurrentL2_permute,
    norm_smul, Real.norm_eq_abs, abs_plaquettePermutationSign, one_mul]

set_option maxHeartbeats 650000 in
theorem wilsonCurrentOSVector_permute {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (τ : Axis) (J : Face) :
    wilsonTransferAxisIsometry μ hl hμ σ τ (wilsonCurrentOSVector μ hl hμ τ J) =
      plaquettePermutationSign σ J • wilsonCurrentOSVector μ hl hμ (σ τ) (permuteFace σ J) := by
  unfold wilsonCurrentOSVector
  rw [wilsonTransferAxisIsometry_ofVector, ← PositiveReflectionForm.ofVector_smul]
  congr 1
  apply Subtype.ext
  exact wilsonCurrentL2_permute μ hμ σ J

end

end GaplessYangMills
