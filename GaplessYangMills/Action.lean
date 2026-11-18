module

public import GaplessYangMills.Wilson
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Differentiating the finite Wilson weight

Under the inverse central change of variables the plaquette contribution to the
logarithm of the unnormalized density differentiates to (β f_p J_p).
-/

@[expose] public section

namespace GaplessYangMills

private theorem hasDerivAt_re_inverse_phase (z : ℂ) (a : ℝ) :
    HasDerivAt (fun t : ℝ => ((Circle.exp (-(t * a)) : ℂ) * z).re) (a * z.im) 0 := by
  have h : (fun t : ℝ => ((Circle.exp (-(t * a)) : ℂ) * z).re) =
      fun t : ℝ => Real.cos (t * a) * z.re + Real.sin (t * a) * z.im := by
    funext t
    rw [Circle.coe_exp, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.cos_neg, Real.sin_neg, neg_mul, sub_neg_eq_add]
  rw [h]
  have hlin := (hasDerivAt_id' (0 : ℝ)).mul_const a
  simpa using (hlin.cos.mul_const z.re).fun_add (hlin.sin.mul_const z.im)

/-- The sign and the rank cancellation in the change of variables in Section 4.
The finite set contains the plaquettes whose weights change. -/
theorem hasDerivAt_inverse_wilson_logWeight {ι : Type*} (S : Finset ι) (trace : ι → ℂ)
    (f : ι → ℝ) (β : ℝ) {N : ℕ} (hN : 0 < N) :
    HasDerivAt (fun t : ℝ =>
      ∑ p ∈ S, (N : ℝ) * β * ((Circle.exp (-(t * (f p / N))) : ℂ) * trace p).re)
      (∑ p ∈ S, β * f p * (trace p).im) 0 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  apply HasDerivAt.fun_sum
  intro p _
  convert (hasDerivAt_re_inverse_phase (trace p) (f p / N)).const_mul ((N : ℝ) * β) using 1
  field_simp

/-- The same derivative for the finite action evaluated on rotated unitary links. -/
theorem hasDerivAt_inverse_wilson_links {N : ℕ} (hN : 0 < N) (β : ℝ)
    (S : Finset (Face × Site)) (U : OneForm (UnitaryMatrix N)) (α : OneForm ℝ) :
    HasDerivAt
      (fun t : ℝ => ∑ p ∈ S, (N : ℝ) * β *
        (plaquetteHolonomy (fun i x =>
          centralPhase N (Circle.exp (-(t * (α i x / N)))) * U i x) p.1 p.2).val.trace.re)
      (∑ p ∈ S, β * d₁ α p.1 p.2 * (plaquetteHolonomy U p.1 p.2).val.trace.im) 0 := by
  have hderiv := hasDerivAt_inverse_wilson_logWeight S
    (fun p => (plaquetteHolonomy U p.1 p.2).val.trace) (fun p => d₁ α p.1 p.2) β hN
  convert hderiv using 1
  funext t
  apply Finset.sum_congr rfl
  rintro ⟨I, x⟩ _
  rw [plaquetteHolonomy_central, trace_centralPhase]
  have hscale : d₁ (fun i y => -(t * (α i y / N))) I x = -(t * (d₁ α I x / N)) := by
    cases I <;> simp only [d₁, diff, Pi.sub_apply] <;> ring
  rw [hscale]

end GaplessYangMills
