module

public import GaplessYangMills.WilsonAxisPermutations
public import GaplessYangMills.WilsonOS

/-!
# Axis symmetry of the physical Wilson transfer

The coordinate permutation carries the positive-time half-space, the
reflection form, and the inward shift to their counterparts in the
permuted direction. It induces an isometric equivalence of the physical
Hilbert spaces and preserves the transfer spectrum.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace Topology

noncomputable section

theorem measurePreserving_permuteConfig {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) : MeasurePreserving (permuteConfig σ) μ.toMeasure μ.toMeasure :=
  ⟨(continuous_permuteConfig σ).measurable,
    congrArg ProbabilityMeasure.toMeasure (periodicWilson_limit_permute β μ hμ σ)⟩

def wilsonPermuteL2 {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) : WilsonL2 μ →ₗᵢ[ℝ] WilsonL2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (permuteConfig σ) (measurePreserving_permuteConfig μ hμ σ)

theorem wilsonPermuteL2_symm {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (u : WilsonL2 μ) :
    wilsonPermuteL2 μ hμ σ (wilsonPermuteL2 μ hμ σ.symm u) = u := by
  let h := measurePreserving_permuteConfig μ hμ σ
  let h' := measurePreserving_permuteConfig μ hμ σ.symm
  change Lp.compMeasurePreserving _ h (Lp.compMeasurePreserving _ h' u) = u
  rw [← Lp.compMeasurePreserving_comp_apply]
  exact (lpComposition_congr (funext (permuteConfig_symm σ)) _ (MeasurePreserving.id μ.toMeasure) u).trans
    (Lp.compMeasurePreserving_id_apply u)

private theorem permuteConfig_gaugeConfig {N : ℕ} (σ : Equiv.Perm Axis) (g : Site → UnitaryMatrix N)
    (U : InfiniteConfig N) :
    permuteConfig σ (gaugeConfig g U) =
      gaugeConfig (fun x => g (permuteSite σ x)) (permuteConfig σ U) := by
  funext p
  obtain ⟨i, x⟩ := p
  simp only [permuteConfig, gaugeConfig, permuteSite_add, permuteSite_step]

private theorem wilsonPermuteL2_toLp {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (f : InfiniteConfig N →ᵇ ℝ) :
    wilsonPermuteL2 μ hμ σ (BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f) =
      BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ
        (f.compContinuous ⟨permuteConfig σ, continuous_permuteConfig σ⟩) := by
  let ha := measurePreserving_permuteConfig μ hμ σ
  let fl := BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f
  let g := f.compContinuous ⟨permuteConfig σ, continuous_permuteConfig σ⟩
  change Lp.compMeasurePreserving _ ha fl = BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ g
  apply Lp.ext
  have hf : (fl : InfiniteConfig N → ℝ) =ᵐ[μ.toMeasure] f :=
    BoundedContinuousFunction.coeFn_toLp 2 μ.toMeasure ℝ f
  filter_upwards [Lp.coeFn_compMeasurePreserving fl ha, ha.quasiMeasurePreserving.ae hf,
    BoundedContinuousFunction.coeFn_toLp 2 μ.toMeasure ℝ g] with U h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

theorem wilsonPermuteL2_halfSpace {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (τ : Axis) {u : WilsonL2 μ} (hu : u ∈ wilsonHalfSpace μ τ) :
    wilsonPermuteL2 μ hμ σ u ∈ wilsonHalfSpace μ (σ τ) := by
  classical
  let I := wilsonPermuteL2 μ hμ σ
  have hclosed := (wilsonHalfSpace_isClosed μ (σ τ)).preimage I.continuous
  apply (closure_minimal (s := ((wilsonHalfSpaceCoreL2 μ τ).range : Set (WilsonL2 μ))) _ hclosed) hu
  rintro _ ⟨f, rfl⟩
  let g : InfiniteConfig N →ᵇ ℝ := f.val.compContinuous ⟨permuteConfig σ, continuous_permuteConfig σ⟩
  have hg : g ∈ wilsonHalfSpaceCore N (σ τ) := by
    constructor
    · obtain ⟨S, hS, hs⟩ := f.property.1
      let E (p : Axis × Site) := (σ p.1, permuteSite σ p.2)
      refine ⟨S.image E, ?_, fun U V h => ?_⟩
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        simpa only [E, permuteSite, Function.comp_apply, Equiv.symm_apply_apply] using hS q hq
      · exact hs _ _ fun p hp => h (E p) (Finset.mem_image_of_mem _ hp)
    · intro k U
      change f.val (permuteConfig σ (gaugeConfig k U)) = f.val (permuteConfig σ U)
      rw [permuteConfig_gaugeConfig]
      exact f.property.2 _ _
  change I (BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f.val) ∈ wilsonHalfSpace μ (σ τ)
  rw [wilsonPermuteL2_toLp]
  exact Submodule.le_topologicalClosure _ ⟨⟨g, hg⟩, rfl⟩

def wilsonHalfSpacePermute {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (τ : Axis) : wilsonHalfSpace μ τ ≃ₗ[ℝ] wilsonHalfSpace μ (σ τ) := by
  let I := wilsonPermuteL2 μ hμ σ
  let f := (I.toLinearMap.comp (wilsonHalfSpace μ τ).subtype).codRestrict (wilsonHalfSpace μ (σ τ))
    (fun u => wilsonPermuteL2_halfSpace μ hμ σ τ u.property)
  refine LinearEquiv.ofBijective f ⟨fun u v h => Subtype.ext (I.injective (congrArg Subtype.val h)), ?_⟩
  intro v
  have hm : wilsonPermuteL2 μ hμ σ.symm v.val ∈ wilsonHalfSpace μ τ := by
    simpa only [Equiv.symm_apply_apply] using wilsonPermuteL2_halfSpace μ hμ σ.symm (σ τ) v.property
  refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
  exact wilsonPermuteL2_symm μ hμ σ v.val

private theorem wilsonPermuteL2_reflect {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (τ : Axis) (c : ℤ) (u : WilsonL2 μ) :
    wilsonPermuteL2 μ hμ σ (wilsonReflectL2 μ hμ τ c u) =
      wilsonReflectL2 μ hμ (σ τ) c (wilsonPermuteL2 μ hμ σ u) := by
  let hp := measurePreserving_permuteConfig μ hμ σ
  let hr := measurePreserving_reflectConfig μ hμ τ c
  let hr' := measurePreserving_reflectConfig μ hμ (σ τ) c
  change Lp.compMeasurePreserving _ hp (Lp.compMeasurePreserving _ hr u) =
    Lp.compMeasurePreserving _ hr' (Lp.compMeasurePreserving _ hp u)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  exact lpComposition_congr (funext (reflectConfig_permuteConfig σ τ c)) _ _ u

private theorem wilsonPermuteL2_shift {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (τ : Axis) (u : WilsonL2 μ) :
    wilsonPermuteL2 μ hμ σ (wilsonTranslateL2 μ hμ (step τ) u) =
      wilsonTranslateL2 μ hμ (step (σ τ)) (wilsonPermuteL2 μ hμ σ u) := by
  let hp := measurePreserving_permuteConfig μ hμ σ
  let hs := measurePreserving_translateConfig μ hμ (step τ)
  let hs' := measurePreserving_translateConfig μ hμ (step (σ τ))
  change Lp.compMeasurePreserving _ hp (Lp.compMeasurePreserving _ hs u) =
    Lp.compMeasurePreserving _ hs' (Lp.compMeasurePreserving _ hp u)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  apply lpComposition_congr _ _ _ u
  funext U
  simpa only [Function.comp_apply, permuteSite_step] using translateConfig_permuteConfig σ (step τ) U

private theorem wilsonOSForm_permute {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (τ : Axis) (u v : wilsonHalfSpace μ τ) :
    (wilsonOSForm μ hl hμ τ).form u v = (wilsonOSForm μ hl hμ (σ τ)).form
      (wilsonHalfSpacePermute μ hμ σ τ u) (wilsonHalfSpacePermute μ hμ σ τ v) := by
  simp only [wilsonOSForm_apply]
  change ⟪wilsonReflectL2 μ hμ τ 0 u.val, v.val⟫_ℝ =
    ⟪wilsonReflectL2 μ hμ (σ τ) 0 (wilsonPermuteL2 μ hμ σ u.val), wilsonPermuteL2 μ hμ σ v.val⟫_ℝ
  rw [← wilsonPermuteL2_reflect]
  exact ((wilsonPermuteL2 μ hμ σ).inner_map_map _ _).symm

set_option maxHeartbeats 800000 in
theorem wilsonTransfer_spectrum_permute {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (τ : Axis) :
    spectrum ℝ (wilsonTransfer hβ μ hl hμ (σ τ)) = spectrum ℝ (wilsonTransfer hβ μ hl hμ τ) := by
  let B := wilsonOSForm μ hl hμ τ
  let C := wilsonOSForm μ hl hμ (σ τ)
  let e := wilsonHalfSpacePermute μ hμ σ τ
  let I := B.hilbertIsometry C e (wilsonOSForm_permute μ hl hμ σ τ)
  let S := wilsonOSShift hβ μ hl hμ τ
  let T := wilsonOSShift hβ μ hl hμ (σ τ)
  have hS (u : wilsonHalfSpace μ τ) : e (S.operator u) = T.operator (e u) :=
    Subtype.ext (wilsonPermuteL2_shift μ hμ σ τ u.val)
  have hI (u : B.Hilbert) : I (S.transfer u) = T.transfer (I u) :=
    B.hilbertIsometry_transfer C e (wilsonOSForm_permute μ hl hμ σ τ) S T hS u
  have he : I.conjStarAlgEquiv S.transfer = T.transfer := by
    ext1 u
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hI, I.apply_symm_apply]
  change spectrum ℝ T.transfer = spectrum ℝ S.transfer
  rw [← he]
  exact AlgEquiv.spectrum_eq I.conjStarAlgEquiv.toAlgEquiv _

end

end GaplessYangMills
