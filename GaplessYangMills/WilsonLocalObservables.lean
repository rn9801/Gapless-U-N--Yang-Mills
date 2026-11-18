module

public import GaplessYangMills.GaugeCylinderDensity
public import GaplessYangMills.WilsonOS

/-!
# Local Wilson observables in time slabs

The flux approximants and centered plaquette currents are bounded
measurable gauge-invariant cylinders. Their slab support gives explicit
positive-time vectors after a translation or a reflection.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem reflectConfig_gaugeConfig {N : ℕ} (τ : Axis) (c : ℤ) (g : Site → UnitaryMatrix N)
    (U : InfiniteConfig N) :
    reflectConfig τ c (gaugeConfig g U) =
      gaugeConfig (g ∘ reflectSiteOn τ c) (reflectConfig τ c U) := by
  funext p
  obtain ⟨i, x⟩ := p
  by_cases hi : i = τ
  · subst i
    simp only [reflectConfig, reflectLinksOn_normal, gaugeConfig, Function.comp_apply,
      reflectSiteOn_add_step_normal, reflectSiteOn_lower_add_step]
    group
  · simp only [reflectConfig, reflectLinksOn_tangent hi, gaugeConfig, Function.comp_apply,
      reflectSiteOn_add_step_tangent hi]

structure WilsonSlabObservable (N : ℕ) (τ : Axis) (lo hi : ℤ) where
  observe : InfiniteConfig N → ℝ
  measurable : Measurable observe
  bounded : ∃ C : ℝ, ∀ U, ‖observe U‖ ≤ C
  invariant : GaugeInvariantObservable observe
  support : ∃ S : Finset InfiniteLink, (∀ p ∈ S, lo ≤ p.2 τ ∧ p.2 τ ≤ hi) ∧
    ∀ U V, (∀ p ∈ S, U p = V p) → observe U = observe V

namespace WilsonSlabObservable

variable {N : ℕ} {τ : Axis} {lo hi : ℤ}

def translate (F : WilsonSlabObservable N τ lo hi) (a : Site) :
    WilsonSlabObservable N τ (lo + a τ) (hi + a τ) where
  observe := fun U => F.observe (translateConfig a U)
  measurable := F.measurable.comp (continuous_translateConfig a).measurable
  bounded := F.bounded.imp (fun _ h U => h (translateConfig a U))
  invariant := F.invariant.translate a
  support := by
    classical
    obtain ⟨S, hT, hs⟩ := F.support
    let e (p : InfiniteLink) := (p.1, p.2 + a)
    refine ⟨S.image e, ?_, fun U V h => hs _ _ fun p hp => h (e p) (Finset.mem_image_of_mem e hp)⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have h := hT q hq
    change lo + a τ ≤ q.2 τ + a τ ∧ q.2 τ + a τ ≤ hi + a τ
    omega

def reflect (F : WilsonSlabObservable N τ lo hi) (c : ℤ) :
    WilsonSlabObservable N τ (c - hi - 1) (c - lo) where
  observe := fun U => F.observe (reflectConfig τ c U)
  measurable := F.measurable.comp (continuous_reflectConfig τ c).measurable
  bounded := F.bounded.imp (fun _ h U => h (reflectConfig τ c U))
  invariant := fun g U => by
    change F.observe (reflectConfig τ c (gaugeConfig g U)) = F.observe (reflectConfig τ c U)
    rw [reflectConfig_gaugeConfig]
    exact F.invariant _ _
  support := by
    classical
    obtain ⟨S, hT, hs⟩ := F.support
    let e := reflectLinkIndex τ c
    refine ⟨S.image e, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have h := hT q hq
      change c - hi - 1 ≤ reflectSiteOn τ (if q.1 = τ then c - 1 else c) q.2 τ ∧
        reflectSiteOn τ (if q.1 = τ then c - 1 else c) q.2 τ ≤ c - lo
      by_cases ht : q.1 = τ <;> simp [reflectSiteOn, ht] <;> omega
    · intro U V h
      apply hs _ _
      intro p hp
      have he := h (e p) (Finset.mem_image_of_mem _ hp)
      simp only [reflectConfig, reflectLinksOn]
      exact congrArg (fun A : UnitaryMatrix N => if p.1 = τ then A⁻¹ else A) he

theorem memLp (F : WilsonSlabObservable N τ lo hi) (μ : ProbabilityMeasure (InfiniteConfig N)) :
    MemLp F.observe 2 μ.toMeasure := by
  obtain ⟨C, h⟩ := F.bounded
  exact MemLp.of_bound F.measurable.aestronglyMeasurable C (ae_of_all _ h)

def toL2 (F : WilsonSlabObservable N τ lo hi) (μ : ProbabilityMeasure (InfiniteConfig N)) : WilsonL2 μ :=
  (F.memLp μ).toLp F.observe

theorem toL2_ae (F : WilsonSlabObservable N τ lo hi) (μ : ProbabilityMeasure (InfiniteConfig N)) :
    (F.toL2 μ : InfiniteConfig N → ℝ) =ᵐ[μ.toMeasure] F.observe :=
  (F.memLp μ).coeFn_toLp

theorem toL2_mem_halfSpace (F : WilsonSlabObservable N τ lo hi) (μ : ProbabilityMeasure (InfiniteConfig N))
    (hlo : 0 ≤ lo) : F.toL2 μ ∈ wilsonHalfSpace μ τ := by
  obtain ⟨C, hC⟩ := F.bounded
  obtain ⟨S, hs, hss⟩ := F.support
  exact mem_wilsonHalfSpace_of_cylinder μ τ F.observe F.measurable (F.memLp μ) C hC F.invariant
    ⟨S, fun p hp => hlo.trans (hs p hp).1, hss⟩

theorem toL2_translate (F : WilsonSlabObservable N τ lo hi) {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (a : Site) :
    (F.translate a).toL2 μ = wilsonTranslateL2 μ hμ a (F.toL2 μ) :=
  (Lp.toLp_compMeasurePreserving (F.memLp μ) (measurePreserving_translateConfig μ hμ a)).symm

theorem toL2_reflect (F : WilsonSlabObservable N τ lo hi) {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (c : ℤ) :
    (F.reflect c).toL2 μ = wilsonReflectL2 μ hμ τ c (F.toL2 μ) :=
  (Lp.toLp_compMeasurePreserving (F.memLp μ) (measurePreserving_reflectConfig μ hμ τ c)).symm

end WilsonSlabObservable

def wilsonFluxApproxObservable (N : ℕ) (τ : Axis) (R : ℕ) (I : Face) :
    WilsonSlabObservable N τ (-((4 * R + 4 : ℕ) : ℤ)) ((4 * R + 4 : ℕ) : ℤ) where
  observe := fun U => averagedFluxApprox iidCutLaw R U I 0
  measurable := measurable_averagedFluxApprox iidCutLaw R I 0
  bounded := (averagedFluxApprox_bounded (N := N) iidCutLaw iidCutLaw_allowed R I 0).imp
    (fun _ h U => (Real.norm_eq_abs _).trans_le (h U))
  invariant := fun g U => congrFun (congrFun (averagedFluxApprox_gaugeConfig iidCutLaw R g U) I) 0
  support := by
    classical
    refine ⟨(edgesNearVertex 0 (4 * R + 4)).image Prod.swap, ?_, ?_⟩
    · intro p hp
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      have h := (mem_edgesNearVertex_iff 0 (4 * R + 4) e).mp he τ
      change -((4 * R + 4 : ℕ) : ℤ) ≤ e.1 τ ∧ e.1 τ ≤ ((4 * R + 4 : ℕ) : ℤ)
      simpa only [Pi.zero_apply, zero_sub, zero_add] using h
    · intro U V h
      exact averagedFluxApprox_congr_box iidCutLaw R I 0 U V fun e he =>
        h e.swap (Finset.mem_image_of_mem Prod.swap he)

def wilsonCurrentObservable {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (τ : Axis)
    (J : Face) : WilsonSlabObservable N τ 0 1 where
  observe := fun U => centeredPlaquetteCurrent μ.toMeasure U (J, 0)
  measurable := (continuous_centeredPlaquetteCurrent μ.toMeasure (J, 0)).measurable
  bounded := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image (continuous_centeredPlaquetteCurrent μ.toMeasure (J, 0)).norm).bddAbove
    exact ⟨C, fun U => hC ⟨U, Set.mem_univ _, rfl⟩⟩
  invariant := fun g U => by
    change centeredPlaquetteCurrent μ.toMeasure (gaugeConfig g U) (J, 0) =
      centeredPlaquetteCurrent μ.toMeasure U (J, 0)
    unfold centeredPlaquetteCurrent plaquetteCurrent
    rw [plaquetteHolonomy_gaugeConfig]
    have h : ((g 0)⁻¹).val * (g 0).val = 1 :=
      congrArg (fun a : UnitaryMatrix N => a.val) (inv_mul_cancel (g 0))
    change (((g 0).val * (plaquetteHolonomy (fun i x => U (i, x)) J 0).val * ((g 0)⁻¹).val).trace.im - _) = _
    rw [Matrix.trace_mul_cycle, h, Matrix.one_mul]
  support := by
    refine ⟨boundaryLinks (J, 0), ?_, ?_⟩
    · intro p hp
      simp only [boundaryLinks, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [step] <;> split <;> norm_num
    · intro U V h
      unfold centeredPlaquetteCurrent plaquetteCurrent
      rw [plaquetteHolonomy_congr_boundary (J, 0) h]

end

end GaplessYangMills
