module

public import GaplessYangMills.WilsonLimits

/-!
# Translation invariance of periodic and limiting Wilson laws
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory Filter
open scoped Topology

def translatePeriodic {L N : ℕ} (a : TorusSite L) (U : TorusConfig L N) : TorusConfig L N :=
  fun (i, x) => U (i, x + a)

def translateConfig {N : ℕ} (a : Site) (U : InfiniteConfig N) : InfiniteConfig N :=
  fun (i, x) => U (i, x + a)

theorem continuous_translateConfig {N : ℕ} (a : Site) :
    Continuous (translateConfig a : InfiniteConfig N → InfiniteConfig N) := by
  apply continuous_pi
  rintro ⟨i, x⟩
  exact continuous_apply (i, x + a)

theorem periodicLogWeight_translate {L N : ℕ} [NeZero L] (β : ℝ)
    (a : TorusSite L) (U : TorusConfig L N) :
    periodicLogWeight β (translatePeriodic a U) = periodicLogWeight β U := by
  have hhol (I : Face) (x : TorusSite L) :
      periodicHolonomy (translatePeriodic a U) I x = periodicHolonomy U I (x + a) := by
    cases I <;> simp only [periodicHolonomy, translatePeriodic, Face.axes, add_right_comm x]
  simp only [periodicLogWeight, hhol]
  congr 1
  let e : Face × TorusSite L ≃ Face × TorusSite L :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.addRight a)
  exact e.sum_comp fun p => (periodicHolonomy U p.1 p.2).val.trace.re

theorem periodicHaar_translate_preserving {L N : ℕ} [NeZero L] (a : TorusSite L) :
    MeasurePreserving (translatePeriodic a : TorusConfig L N → TorusConfig L N)
      (periodicHaar L N) (periodicHaar L N) := by
  let e : TorusLink L ≃ TorusLink L := Equiv.prodCongr (Equiv.refl _) (Equiv.addRight a)
  have he : ⇑(MeasurableEquiv.piCongrLeft (fun _ : TorusLink L => UnitaryMatrix N) e.symm) =
      (translatePeriodic a : TorusConfig L N → TorusConfig L N) := by
    funext U p
    rcases p with ⟨i, x⟩
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : TorusLink L => UnitaryMatrix N) e.symm U (e (i, x))
    simpa [e, translatePeriodic] using h
  rw [← he]
  exact measurePreserving_piCongrLeft (fun _ : TorusLink L => unitaryHaar N) e.symm

theorem periodicWilson_translate_preserving {L N : ℕ} [NeZero L] (β : ℝ) (a : TorusSite L) :
    MeasurePreserving (translatePeriodic a : TorusConfig L N → TorusConfig L N)
      (periodicWilson L N β) (periodicWilson L N β) := by
  have ht := periodicHaar_translate_preserving (N := N) a
  refine ⟨ht.measurable, Measure.ext_of_lintegral _ ?_⟩
  intro g hg
  rw [lintegral_map hg ht.measurable, periodicWilson, lintegral_smul_measure,
    lintegral_smul_measure]
  have hw : Measurable (periodicWeight β : TorusConfig L N → _) := periodicWeight_measurable β
  have hg' : Measurable (fun U => g (translatePeriodic a U)) := hg.comp ht.measurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hg', lintegral_withDensity_eq_lintegral_mul _ hw hg]
  congr 1
  simpa only [Pi.mul_apply, periodicWeight, periodicLogWeight_translate] using
    ht.lintegral_comp (hw.mul hg)

theorem extendedWilson_translate {L N : ℕ} [NeZero L] (β : ℝ) (a : Site) :
    ProbabilityMeasure.map (extendedWilson L N β) (translateConfig a) =
      extendedWilson L N β := by
  let t : TorusSite L := fun j => (a j : ZMod L)
  have hf : (translateConfig a : InfiniteConfig N → InfiniteConfig N) ∘ extendPeriodic =
      extendPeriodic ∘ translatePeriodic t := by
    funext U p
    rcases p with ⟨i, x⟩
    simp only [Function.comp_apply, translateConfig, extendPeriodic, translatePeriodic,
      Pi.add_apply, Int.cast_add, t]
    rfl
  apply Subtype.ext
  change Measure.map (translateConfig a) (Measure.map extendPeriodic (periodicWilson L N β)) =
    Measure.map extendPeriodic (periodicWilson L N β)
  have he := (continuous_extendPeriodic L N).measurable
  have ht := periodicWilson_translate_preserving (N := N) β t
  rw [Measure.map_map (continuous_translateConfig a).measurable he, hf,
    ← Measure.map_map he ht.measurable, ht.map_eq]

/-- Every weak limit of the periodic laws is invariant under all lattice
translations. -/
theorem periodicWilson_limit_translate {N : ℕ} (β : ℝ) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (a : Site) :
    ProbabilityMeasure.map μ (translateConfig a) = μ := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ
    (continuous_translateConfig a)
  simp only [extendedWilson_translate] at h
  exact tendsto_nhds_unique h hμ

end GaplessYangMills
