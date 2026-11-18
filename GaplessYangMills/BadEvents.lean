module

public import GaplessYangMills.WilsonLimits
public import GaplessYangMills.WeakCoupling
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

/-!
# Openness of the bad-plaquette event

For a positive-rank unitary matrix, a principal eigenangle exceeds the cutoff
in absolute value exactly when the squared operator distance to the identity
exceeds twice the scalar penalty.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix.Norms.L2Operator

def badUnitary {N : ℕ} (U : UnitaryMatrix N) : Prop :=
  ∃ z ∈ U.val.charpoly.roots, Real.pi / 4 < |Complex.arg z|

private theorem badRoot_iff {z : ℂ} (hz : ‖z‖ = 1) :
    Real.pi / 4 < |Complex.arg z| ↔ z.re < Real.cos (Real.pi / 4) := by
  let w : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  have hc := congrArg (fun w : Circle => (w : ℂ).re) (Circle.exp_arg w)
  change ((Circle.exp (Complex.arg z) : Circle) : ℂ).re = z.re at hc
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, ← Real.cos_abs] at hc
  have ha : |Complex.arg z| ∈ Set.Icc 0 Real.pi := ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hb : Real.pi / 4 ∈ Set.Icc 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
  rw [← hc]
  exact (Real.strictAntiOn_cos.lt_iff_gt ha hb).symm

theorem badUnitary_iff_norm {N : ℕ} (hN : 0 < N) (U : UnitaryMatrix N) :
    badUnitary U ↔ 2 * badPenalty < ‖U.val - 1‖ ^ 2 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨r, hr⟩ := ((spectrum.isCompact (𝕜 := ℂ) U.val).image
    Complex.continuous_re).exists_isLeast ((spectrum.nonempty U.val).image _)
  rw [Unitary.norm_sub_one_sq_eq U.property hr]
  have hroot {z : ℂ} : z ∈ U.val.charpoly.roots ↔ z ∈ spectrum ℂ U.val := by
    rw [Polynomial.mem_roots U.val.charpoly_monic.ne_zero, Matrix.mem_spectrum_iff_isRoot_charpoly]
  unfold badUnitary badPenalty
  constructor
  · rintro ⟨z, hz, hangle⟩
    have h := (badRoot_iff (norm_charpoly_root U hz)).mp hangle
    have hmin := hr.2 ⟨z, hroot.mp hz, rfl⟩
    linarith
  · intro h
    obtain ⟨z, hz, hzr⟩ := hr.1
    refine ⟨z, hroot.mpr hz, (badRoot_iff (spectrum.norm_eq_one_of_unitary U.property hz)).mpr ?_⟩
    linarith

theorem isOpen_badUnitary {N : ℕ} (hN : 0 < N) : IsOpen {U : UnitaryMatrix N | badUnitary U} := by
  have he : {U : UnitaryMatrix N | badUnitary U} =
      {U : UnitaryMatrix N | 2 * badPenalty < ‖U.val - 1‖ ^ 2} := by
    ext U
    exact badUnitary_iff_norm hN U
  rw [he]
  exact isOpen_lt continuous_const ((continuous_subtype_val.sub continuous_const).norm.pow 2)

def badPlaquette {N : ℕ} (p : Plaquette) : Set (InfiniteConfig N) :=
  {U | badUnitary (plaquetteHolonomy (fun i x => U (i, x)) p.1 p.2)}

theorem continuous_plaquetteHolonomy {N : ℕ} (p : Plaquette) :
    Continuous (fun U : InfiniteConfig N => plaquetteHolonomy (fun i x => U (i, x)) p.1 p.2) := by
  have h (i : Axis) (x : Site) : Continuous (fun U : InfiniteConfig N => U (i, x)) :=
    continuous_apply (i, x)
  change Continuous (fun U : InfiniteConfig N => U (p.1.axes.1, p.2) *
    U (p.1.axes.2, p.2 + step p.1.axes.1) * (U (p.1.axes.1, p.2 + step p.1.axes.2))⁻¹ *
    (U (p.1.axes.2, p.2))⁻¹)
  exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv

theorem isOpen_badPlaquette {N : ℕ} (hN : 0 < N) (p : Plaquette) :
    IsOpen (badPlaquette (N := N) p) :=
  (isOpen_badUnitary hN).preimage (continuous_plaquetteHolonomy p)

theorem isOpen_allBadPlaquettes {N : ℕ} (hN : 0 < N) (S : Finset Plaquette) :
    IsOpen (allBad (badPlaquette (N := N)) S) := by
  have he : allBad (badPlaquette (N := N)) S = ⋂ p ∈ S, badPlaquette p := by
    ext U
    simp [allBad]
  rw [he]
  exact S.finite_toSet.isOpen_biInter (fun p _ => isOpen_badPlaquette hN p)

end GaplessYangMills
