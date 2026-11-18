module

public import GaplessYangMills.WilsonReflections
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Splitting the Haar reference across a reflection

The negative half is parameterized by reflecting the positive coordinates,
with inversion on the normal links. The two halves have identical product
Haar laws. At a site cut, integrating a product of equal half-observables
with the shared boundary held fixed gives a square.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory

noncomputable section

def assembleReflection {B P I : Type*} {N : ℕ} (e : B ⊕ (P ⊕ P) ≃ I)
    (normal : P → Bool) (q : (B → UnitaryMatrix N) × ((P → UnitaryMatrix N) × (P → UnitaryMatrix N))) :
    I → UnitaryMatrix N :=
  fun i => match e.symm i with
    | .inl b => q.1 b
    | .inr (.inl p) => q.2.1 p
    | .inr (.inr p) => if normal p then (q.2.2 p)⁻¹ else q.2.2 p

@[simp] theorem assembleReflection_boundary {B P I : Type*} {N : ℕ} (e : B ⊕ (P ⊕ P) ≃ I)
    (normal : P → Bool) (q : (B → UnitaryMatrix N) × ((P → UnitaryMatrix N) × (P → UnitaryMatrix N)))
    (b : B) :
    assembleReflection e normal q (e (.inl b)) = q.1 b := by
  simp [assembleReflection]

@[simp] theorem assembleReflection_positive {B P I : Type*} {N : ℕ} (e : B ⊕ (P ⊕ P) ≃ I)
    (normal : P → Bool) (q : (B → UnitaryMatrix N) × ((P → UnitaryMatrix N) × (P → UnitaryMatrix N)))
    (p : P) :
    assembleReflection e normal q (e (.inr (.inl p))) = q.2.1 p := by
  simp [assembleReflection]

@[simp] theorem assembleReflection_negative {B P I : Type*} {N : ℕ} (e : B ⊕ (P ⊕ P) ≃ I)
    (normal : P → Bool) (q : (B → UnitaryMatrix N) × ((P → UnitaryMatrix N) × (P → UnitaryMatrix N)))
    (p : P) :
    assembleReflection e normal q (e (.inr (.inr p))) = if normal p then (q.2.2 p)⁻¹ else q.2.2 p := by
  simp [assembleReflection]

theorem continuous_assembleReflection {B P I : Type*} {N : ℕ}
    (e : B ⊕ (P ⊕ P) ≃ I) (normal : P → Bool) :
    Continuous (assembleReflection (N := N) e normal) := by
  apply continuous_pi
  intro i
  obtain ⟨v, rfl⟩ := e.surjective i
  rcases v with b | p | p
  · simp only [assembleReflection_boundary]
    exact (continuous_apply b).comp continuous_fst
  · simp only [assembleReflection_positive]
    exact (continuous_apply p).comp (continuous_fst.comp continuous_snd)
  · by_cases hp : normal p
    · simp only [assembleReflection_negative, ite_eq_left hp]
      exact ((continuous_apply p).comp (continuous_snd.comp continuous_snd)).inv
    · simp only [assembleReflection_negative, ite_eq_right hp]
      exact (continuous_apply p).comp (continuous_snd.comp continuous_snd)

theorem measurePreserving_assembleReflection {B P I : Type*} [Fintype B] [Fintype P] [Fintype I]
    {N : ℕ} (e : B ⊕ (P ⊕ P) ≃ I) (normal : P → Bool) :
    MeasurePreserving (assembleReflection (N := N) e normal)
      ((Measure.pi fun _ : B => unitaryHaar N).prod
        ((Measure.pi fun _ : P => unitaryHaar N).prod (Measure.pi fun _ : P => unitaryHaar N)))
      (Measure.pi fun _ : I => unitaryHaar N) := by
  let mB := Measure.pi fun _ : B => unitaryHaar N
  let mP := Measure.pi fun _ : P => unitaryHaar N
  let flip (x : P → UnitaryMatrix N) (p : P) := if normal p then (x p)⁻¹ else x p
  have hflip : MeasurePreserving flip mP mP := by
    refine measurePreserving_pi (fun _ : P => unitaryHaar N) (fun _ => unitaryHaar N)
      (f := fun p g => if normal p then g⁻¹ else g) (fun p => ?_)
    by_cases hp : normal p
    · simp only [ite_eq_left hp]
      exact Measure.measurePreserving_inv (unitaryHaar N)
    · simp only [ite_eq_right hp]
      exact MeasurePreserving.id (unitaryHaar N)
  let j := MeasurableEquiv.sumPiEquivProdPi (fun _ : P ⊕ P => UnitaryMatrix N)
  let k := MeasurableEquiv.sumPiEquivProdPi (fun _ : B ⊕ (P ⊕ P) => UnitaryMatrix N)
  let t := MeasurableEquiv.piCongrLeft (fun _ : I => UnitaryMatrix N) e
  have hj : MeasurePreserving j.symm (mP.prod mP) (Measure.pi fun _ : P ⊕ P => unitaryHaar N) :=
    measurePreserving_sumPiEquivProdPi_symm fun _ => unitaryHaar N
  have hk : MeasurePreserving k.symm (mB.prod (Measure.pi fun _ : P ⊕ P => unitaryHaar N))
      (Measure.pi fun _ : B ⊕ (P ⊕ P) => unitaryHaar N) :=
    measurePreserving_sumPiEquivProdPi_symm fun _ => unitaryHaar N
  have ht : MeasurePreserving t (Measure.pi fun _ : B ⊕ (P ⊕ P) => unitaryHaar N)
      (Measure.pi fun _ : I => unitaryHaar N) :=
    measurePreserving_piCongrLeft (fun _ => unitaryHaar N) e
  have hm := ht.comp (hk.comp ((MeasurePreserving.id mB).prod
    (hj.comp ((MeasurePreserving.id mP).prod hflip))))
  convert hm using 1
  funext q i
  obtain ⟨v, rfl⟩ := e.surjective i
  have he := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : I => UnitaryMatrix N)
    e (k.symm (q.1, j.symm (q.2.1, flip q.2.2))) v
  rw [show (t ∘ _) q (e v) = t (k.symm (q.1, j.symm (q.2.1, flip q.2.2))) (e v) from rfl, he]
  rcases v with b | p | p <;> simp only [assembleReflection_boundary, assembleReflection_positive,
    assembleReflection_negative, j, k, flip, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk]

theorem integral_reflection_square_nonneg {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
    [CompactSpace B] [CompactSpace X] [MeasurableSpace B] [MeasurableSpace X]
    [BorelSpace B] [BorelSpace X] [SecondCountableTopology B] [SecondCountableTopology X]
    (μ : Measure B) (ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (w : B → ℝ) (hw : Continuous w) (hw₀ : ∀ b, 0 ≤ w b)
    (A : B × X → ℝ) (hA : Continuous A) :
    0 ≤ ∫ q : B × (X × X), w q.1 * (A (q.1, q.2.1) * A (q.1, q.2.2)) ∂μ.prod (ν.prod ν) := by
  let F (q : B × (X × X)) := w q.1 * (A (q.1, q.2.1) * A (q.1, q.2.2))
  have hF : Continuous F :=
    (hw.comp continuous_fst).mul
      ((hA.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
        (hA.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  change 0 ≤ ∫ q, F q ∂μ.prod (ν.prod ν)
  rw [integral_prod F (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F))]
  apply integral_nonneg
  intro b
  change 0 ≤ ∫ q : X × X, w b * (A (b, q.1) * A (b, q.2)) ∂ν.prod ν
  rw [integral_const_mul]
  have he := integral_prod_mul (μ := ν) (ν := ν) (fun x => A (b, x)) (fun x => A (b, x))
  rw [show (∫ q : X × X, A (b, q.1) * A (b, q.2) ∂ν.prod ν) =
      (∫ x, A (b, x) ∂ν) * (∫ x, A (b, x) ∂ν) from he]
  exact mul_nonneg (hw₀ b) (mul_self_nonneg _)

end

end GaplessYangMills
