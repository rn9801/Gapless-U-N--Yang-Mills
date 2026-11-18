module

public import GaplessYangMills.Eigenangles
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.ZMod.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

/-!
# The periodic Wilson probability law

Positive links are the independent Haar coordinates. The Wilson density uses
each positive plaquette once, with exponent `N * β`.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped ENNReal

noncomputable section

instance unitaryCompact (N : ℕ) : CompactSpace (UnitaryMatrix N) := by
  apply isCompact_iff_compactSpace.mp
  let C : Set (Matrix (Fin N) (Fin N) ℂ) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1))
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  apply hC.of_isClosed_subset isClosed_unitary
  intro U hU i _ j _
  exact mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hU i j)

instance unitarySecondCountable (N : ℕ) : SecondCountableTopology (UnitaryMatrix N) := by
  let : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  exact (Topology.IsEmbedding.subtypeVal (p := fun U : Matrix (Fin N) (Fin N) ℂ =>
    U ∈ unitary (Matrix (Fin N) (Fin N) ℂ))).secondCountableTopology

instance unitaryMeasurable (N : ℕ) : MeasurableSpace (UnitaryMatrix N) := borel _
instance unitaryBorel (N : ℕ) : BorelSpace (UnitaryMatrix N) := ⟨rfl⟩

def unitaryHaar (N : ℕ) : Measure (UnitaryMatrix N) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance unitaryHaar_probability (N : ℕ) : IsProbabilityMeasure (unitaryHaar N) :=
  ⟨Measure.haarMeasure_self⟩

abbrev TorusSite (L : ℕ) := Axis → ZMod L
abbrev TorusLink (L : ℕ) := Axis × TorusSite L
abbrev TorusConfig (L N : ℕ) := TorusLink L → UnitaryMatrix N

def torusStep (L : ℕ) (i : Axis) : TorusSite L := fun j => if i = j then 1 else 0

def periodicHolonomy {L N : ℕ} (U : TorusConfig L N) (I : Face) (x : TorusSite L) :
    UnitaryMatrix N :=
  let (i, j) := I.axes
  U (i, x) * U (j, x + torusStep L i) * (U (i, x + torusStep L j))⁻¹ * (U (j, x))⁻¹

theorem continuous_periodicHolonomy {L N : ℕ} (I : Face) (x : TorusSite L) :
    Continuous (fun U : TorusConfig L N => periodicHolonomy U I x) := by
  have h (e : TorusLink L) : Continuous (fun U : TorusConfig L N => U e) :=
    continuous_apply e
  change Continuous (fun U : TorusConfig L N =>
    U (I.axes.1, x) * U (I.axes.2, x + torusStep L I.axes.1) *
      (U (I.axes.1, x + torusStep L I.axes.2))⁻¹ * (U (I.axes.2, x))⁻¹)
  exact (((h _).mul (h _)).mul (h _).inv).mul (h _).inv

def periodicLogWeight {L N : ℕ} [NeZero L] (β : ℝ) (U : TorusConfig L N) : ℝ :=
  (N : ℝ) * β * ∑ p : Face × TorusSite L, (periodicHolonomy U p.1 p.2).val.trace.re

theorem continuous_periodicLogWeight {L N : ℕ} [NeZero L] (β : ℝ) :
    Continuous (periodicLogWeight β : TorusConfig L N → ℝ) := by
  unfold periodicLogWeight
  apply continuous_const.mul
  apply continuous_finsetSum
  intro p _
  exact Complex.continuous_re.comp (Continuous.matrix_trace
    (continuous_subtype_val.comp (continuous_periodicHolonomy p.1 p.2)))

def periodicHaar (L N : ℕ) [NeZero L] : Measure (TorusConfig L N) :=
  Measure.pi fun _ => unitaryHaar N

instance periodicHaar_probability (L N : ℕ) [NeZero L] :
    IsProbabilityMeasure (periodicHaar L N) := by
  unfold periodicHaar
  infer_instance


instance unitaryHaar_leftInvariant (N : ℕ) : Measure.IsMulLeftInvariant (unitaryHaar N) := by
  unfold unitaryHaar
  infer_instance

theorem periodicHaar_mulLeft_preserving {L N : ℕ} [NeZero L] (A : TorusConfig L N) :
    MeasurePreserving (fun U => A * U) (periodicHaar L N) (periodicHaar L N) :=
  measurePreserving_pi _ _ (fun e => measurePreserving_mul_left (unitaryHaar N) (A e))

def periodicWeight {L N : ℕ} [NeZero L] (β : ℝ) (U : TorusConfig L N) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (periodicLogWeight β U))


theorem periodicWeight_measurable {L N : ℕ} [NeZero L] (β : ℝ) :
    Measurable (periodicWeight β : TorusConfig L N → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp (continuous_periodicLogWeight β)).measurable)

def periodicPartition (L N : ℕ) [NeZero L] (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ U, periodicWeight β U ∂periodicHaar L N

theorem periodicPartition_pos (L N : ℕ) [NeZero L] (β : ℝ) :
    0 < periodicPartition L N β := by
  unfold periodicPartition
  rw [lintegral_pos_iff_support (periodicWeight_measurable β)]
  simp [Function.support, periodicWeight, Real.exp_pos]

theorem periodicPartition_lt_top (L N : ℕ) [NeZero L] (β : ℝ) :
    periodicPartition L N β < ⊤ := by
  have hc : Continuous (fun U : TorusConfig L N => Real.exp (periodicLogWeight β U)) :=
    Real.continuous_exp.comp (continuous_periodicLogWeight β)
  obtain ⟨C, hC⟩ := (isCompact_univ.image hc).bddAbove
  have h : ∀ U : TorusConfig L N, periodicWeight β U ≤ ENNReal.ofReal C :=
    fun U => ENNReal.ofReal_le_ofReal (hC ⟨U, Set.mem_univ _, rfl⟩)
  refine (lintegral_mono h).trans_lt ?_
  simp

/-- Wilson probability on the periodic four-dimensional lattice. -/
def periodicWilson (L N : ℕ) [NeZero L] (β : ℝ) : Measure (TorusConfig L N) :=
  (periodicPartition L N β)⁻¹ • (periodicHaar L N).withDensity (periodicWeight β)

instance periodicWilson_probability (L N : ℕ) [NeZero L] (β : ℝ) :
    IsProbabilityMeasure (periodicWilson L N β) := by
  refine ⟨?_⟩
  simp only [periodicWilson, smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change (periodicPartition L N β)⁻¹ * periodicPartition L N β = 1
  exact ENNReal.inv_mul_cancel (periodicPartition_pos L N β).ne'
    (periodicPartition_lt_top L N β).ne


/-- A fixed rotation of the positive links translates the Boltzmann density by
the inverse rotation. This is the finite-volume change of variables. -/
theorem lintegral_periodicWilson_mulLeft {L N : ℕ} [NeZero L] (β : ℝ)
    (A : TorusConfig L N) {g : TorusConfig L N → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ U, g (A * U) ∂periodicWilson L N β) =
      (periodicPartition L N β)⁻¹ *
        ∫⁻ U, periodicWeight β (A⁻¹ * U) * g U ∂periodicHaar L N := by
  rw [periodicWilson, lintegral_smul_measure]
  have hA := periodicHaar_mulLeft_preserving A
  have hAi := periodicHaar_mulLeft_preserving A⁻¹
  have hw : Measurable (periodicWeight β : TorusConfig L N → ℝ≥0∞) :=
    periodicWeight_measurable β
  have hmeas : Measurable (fun U => g (A * U)) := hg.comp hA.measurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hmeas]
  have hchange := hA.lintegral_comp ((hw.comp hAi.measurable).mul hg)
  exact congrArg ((periodicPartition L N β)⁻¹ * ·) (by simpa [mul_assoc] using hchange)

end

end GaplessYangMills
