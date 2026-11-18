module

public import GaplessYangMills.KernelCycleEstimate
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.ZMod.Basic

/-!
# Cyclic products under independent slice measures

The iterated kernel cycle integral is the integral of the cyclic product
over the finite product of the slice measures.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory

noncomputable section

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [CompactSpace X] [BorelSpace X] in
private theorem integral_finCons {n : ℕ} (f : (Fin (n + 1) → X) → ℝ) :
    (∫ p : X × (Fin n → X), f (Fin.cons (α := fun _ => X) p.1 p.2) ∂μ.prod (Measure.pi fun _ => μ)) =
      ∫ x, f x ∂Measure.pi (fun _ => μ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm e
  have he (p : X × (Fin n → X)) : e.symm p = Fin.cons (α := fun _ => X) p.1 p.2 :=
    Fin.insertNth_zero' p.1 p.2
  simpa only [he] using h.integral_comp' f

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem continuous_finCons {n : ℕ} :
    Continuous (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2) := by
  refine continuous_pi fun i => Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp continuous_snd

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem continuous_pathProduct {n : ℕ} (K : Fin (n + 1) → X → X → ℝ)
    (hK : ∀ i, Continuous (fun p : X × X => K i p.1 p.2)) :
    Continuous (fun p : X × (Fin n → X) × X =>
      ∏ i, K i (Fin.cons (α := fun _ => X) p.1 p.2.1 i) (Fin.snoc (α := fun _ => X) p.2.1 p.2.2 i)) := by
  have hcons (i : Fin (n + 1)) : Continuous (fun p : X × (Fin n → X) × X =>
      Fin.cons (α := fun _ => X) p.1 p.2.1 i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd.fst
  have hsnoc (i : Fin (n + 1)) : Continuous (fun p : X × (Fin n → X) × X =>
      Fin.snoc (α := fun _ => X) p.2.1 p.2.2 i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (continuous_snd.snd :
        Continuous (fun p : X × (Fin n → X) × X => p.2.2))
    · simp only [Fin.snoc_castSucc]
      exact (continuous_apply j).comp continuous_snd.fst
  exact continuous_finsetProd _ fun i _ => (hK i).comp ((hcons i).prodMk (hsnoc i))

/-- The open path integral is the integral over its independent intermediate
slices. The endpoint slices are held fixed. -/
theorem kernelPath_eq_integral_prod {n : ℕ} (K : Fin (n + 1) → X → X → ℝ)
    (hK : ∀ i, Continuous (fun p : X × X => K i p.1 p.2)) (a b : X) :
    kernelPath μ (K 0) (List.ofFn fun i : Fin n => K i.succ) a b =
      ∫ x : Fin n → X, ∏ i, K i (Fin.cons (α := fun _ => X) a x i) (Fin.snoc (α := fun _ => X) x b i)
        ∂Measure.pi (fun _ => μ) := by
  induction n generalizing a with
  | zero =>
    have hs (x : Fin 0 → X) : Fin.snoc (α := fun _ => X) x b 0 = b :=
      Fin.snoc_last (α := fun _ => X) b x
    simp [hs]
  | succ n ih =>
    let f (x : Fin (n + 1) → X) :=
      ∏ i, K i (Fin.cons (α := fun _ => X) a x i) (Fin.snoc (α := fun _ => X) x b i)
    have hf : Continuous f := (continuous_pathProduct K hK).comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))
    have hi : Integrable (fun p : X × (Fin n → X) => f (Fin.cons (α := fun _ => X) p.1 p.2))
        (μ.prod (Measure.pi fun _ => μ)) :=
      (hf.comp continuous_finCons).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    change _ = ∫ x, f x ∂Measure.pi (fun _ => μ)
    rw [← integral_finCons μ f, integral_prod _ hi, List.ofFn_succ, kernelPath_cons]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [ih (fun i => K i.succ) (fun i => hK i.succ), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [f, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      ← Fin.cons_snoc_eq_snoc_cons]

/-- The ordered kernel cycle is the integral of the product over periodic
nearest-neighbor slice pairs. -/
theorem kernelCycleIntegral_eq_integral_prod {n : ℕ} (K : Fin (n + 1) → X → X → ℝ)
    (hK : ∀ i, Continuous (fun p : X × X => K i p.1 p.2)) :
    kernelCycleIntegral μ (K 0) (List.ofFn fun i : Fin n => K i.succ) =
      ∫ x : Fin (n + 1) → X, ∏ i, K i (x i) (x (i + 1)) ∂Measure.pi (fun _ => μ) := by
  let f (x : Fin (n + 1) → X) := ∏ i, K i (x i) (x (i + 1))
  have hf : Continuous f := by
    apply continuous_finsetProd
    intro i _
    let g (x : Fin (n + 1) → X) := (x i, x (i + 1))
    have hg : Continuous g := (continuous_apply i).prodMk (continuous_apply (i + 1))
    exact (hK i).comp hg
  have hi : Integrable (fun p : X × (Fin n → X) => f (Fin.cons (α := fun _ => X) p.1 p.2))
      (μ.prod (Measure.pi fun _ => μ)) :=
    (hf.comp continuous_finCons).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change _ = ∫ x, f x ∂Measure.pi (fun _ => μ)
  rw [← integral_finCons μ f, integral_prod _ hi, kernelCycleIntegral]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [kernelPath_eq_integral_prod μ K hK]
  apply integral_congr_ae
  filter_upwards [] with x
  apply Finset.prod_congr rfl
  intro i _
  change K i (Fin.cons (α := fun _ => X) a x i) (Fin.snoc (α := fun _ => X) x a i) =
    K i (Fin.cons (α := fun _ => X) a x i) (Fin.cons (α := fun _ => X) a x (i + 1))
  congr 1
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.last_add_one, Fin.snoc_last, Fin.cons_zero]
  · rw [Fin.coeSucc_eq_succ, Fin.snoc_castSucc, Fin.cons_succ]

/-- Sample matrix order bounds the integral of a product around an even
periodic direction by the corresponding product of the reference kernel. -/
theorem integral_zmodCycle_le_of_sampleOrder {L : ℕ} [NeZero L]
    (hL : Even L) (K : ZMod L → X → X → ℝ) (R : X → X → ℝ)
    (hK : ∀ t, Continuous (fun p : X × X => K t p.1 p.2))
    (hR : Continuous (fun p : X × X => R p.1 p.2))
    (hpos : ∀ (m : ℕ) (v : Fin m → X) t,
      (Matrix.of fun a b => K t (v a) (v b)).PosSemidef)
    (horder : ∀ (m : ℕ) (v : Fin m → X) t,
      ((Matrix.of fun a b => R (v a) (v b)) -
        (Matrix.of fun a b => K t (v a) (v b))).PosSemidef) :
    (∫ a : ZMod L → X, ∏ t, K t (a t) (a (t + 1)) ∂Measure.pi (fun _ => μ)) ≤
      ∫ a : ZMod L → X, ∏ t, R (a t) (a (t + 1)) ∂Measure.pi (fun _ => μ) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    let e := ZMod.finEquiv (n + 1)
    let em := MeasurableEquiv.piCongrLeft (fun _ : ZMod (n + 1) => X) e.toEquiv
    have hp : MeasurePreserving em (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
      measurePreserving_piCongrLeft (fun _ => μ) e.toEquiv
    have hchange (F : ZMod (n + 1) → X → X → ℝ) :
        (∫ a : ZMod (n + 1) → X, ∏ t, F t (a t) (a (t + 1)) ∂Measure.pi (fun _ => μ)) =
          ∫ a : Fin (n + 1) → X, ∏ t, F (e t) (a t) (a (t + 1)) ∂Measure.pi (fun _ => μ) := by
      rw [← hp.integral_comp' (fun a => ∏ t, F t (a t) (a (t + 1)))]
      apply integral_congr_ae
      filter_upwards [] with a
      rw [← e.toEquiv.prod_comp (fun t => F t (em a t) (em a (t + 1)))]
      apply Finset.prod_congr rfl
      intro t _
      change F (e t) (em a (e t)) (em a (e t + 1)) = F (e t) (a t) (a (t + 1))
      have he (i : Fin (n + 1)) : em a (e i) = a i :=
        MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => X) e.toEquiv a i
      rw [he t, ← map_one e, ← map_add, he (t + 1)]
    rw [hchange K, hchange (fun _ => R)]
    rw [← kernelCycleIntegral_eq_integral_prod μ (fun t => K (e t)) (fun t => hK (e t)),
      ← kernelCycleIntegral_eq_integral_prod μ (fun _ : Fin (n + 1) => R) (fun _ => hR)]
    let js := List.ofFn fun i : Fin n => e i.succ
    have hjs : js.length = n := List.length_ofFn
    obtain ⟨k, hk⟩ := hL
    have hk₀ : 0 < k := by omega
    have hlen : (e 0 :: js).length = 2 * k := by simp only [List.length_cons, hjs]; omega
    have h := kernelCycleIntegral_le_of_sampleOrder μ K R hK hR hpos horder (e 0) js hk₀ hlen
    simpa only [js, List.map_ofFn, Function.comp_def, hjs, List.ofFn_const] using h

end

end GaplessYangMills
