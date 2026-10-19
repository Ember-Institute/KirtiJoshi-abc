import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPreTiltCompleteness

/-!
source-id: JT-SCENE1-GEOMETRIC-PRETILT-DIVISION
source: Joshi tilt/untilt norm compatibility; actual PreTilt coefficients,
Frobenius and compatible integral roots. Original proofs.
fidelity: constructs division approximations inside the original PreTilt
when the numerator norm is at most the denominator norm. The error vanishes
at any prescribed coefficient and has the exact coefficient-ball bound.
No valuation-ring or divisibility certificate is assumed. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricPreTiltDivision

open JoshiTeich.Prologue
open scoped NNReal
universe u
noncomputable section
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω] [CompleteSpace Ω]
variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

/-- Canonical untilt in the n-th inverse Frobenius position. -/
def shiftedUntilt (x : GeometricTiltField.Source Ω p) (n : ℕ) :
    LocalGeometricFontaine.integerRing Ω :=
  PreTilt.untilt (((frobeniusEquiv (GeometricTiltField.Source Ω p) p).symm^[n]) x)

theorem shiftedUntilt_reduction (x : GeometricTiltField.Source Ω p) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)})
      (shiftedUntilt Ω p x n) = PreTilt.coeff n x := by
  rw [shiftedUntilt, PreTilt.mk_untilt_eq_coeff_zero]
  simpa only [Nat.zero_add] using PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x

theorem shiftedUntilt_norm_pow (x : GeometricTiltField.Source Ω p) (n : ℕ) :
    ‖(shiftedUntilt Ω p x n : Ω)‖ ^ p ^ n = ‖x‖ := by
  have h := congrArg (fun z : LocalGeometricFontaine.integerRing Ω => (z : Ω))
    (PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n)
  have hpow : (shiftedUntilt Ω p x n : Ω) ^ p ^ n =
      (PreTilt.untilt x : LocalGeometricFontaine.integerRing Ω) := by
    simpa only [shiftedUntilt, Subring.coe_pow] using h
  rw [← norm_pow, hpow, GeometricPreTiltCompleteness.norm_eq_valuation,
    GeometricTiltSharp.sourceValuation_eq_sharp_norm]
  rfl

theorem shiftedUntilt_ne_zero (x : GeometricTiltField.Source Ω p) (hx : x ≠ 0) (n : ℕ) :
    (shiftedUntilt Ω p x n : Ω) ≠ 0 := by
  intro h
  have hz := shiftedUntilt_norm_pow Ω p x n
  rw [h, norm_zero, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at hz
  exact hx (norm_eq_zero.mp hz.symm)

theorem shiftedUntilt_norm_le (a b : GeometricTiltField.Source Ω p) (hab : ‖a‖ ≤ ‖b‖) (n : ℕ) :
    ‖(shiftedUntilt Ω p a n : Ω)‖ ≤ ‖(shiftedUntilt Ω p b n : Ω)‖ := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
  rwa [shiftedUntilt_norm_pow, shiftedUntilt_norm_pow]

/-- An integral actual untilt quotient at the n-th position. -/
def quotientLift (a b : GeometricTiltField.Source Ω p) (hb : b ≠ 0) (hab : ‖a‖ ≤ ‖b‖)
    (n : ℕ) : LocalGeometricFontaine.integerRing Ω :=
  ⟨(shiftedUntilt Ω p a n : Ω) / (shiftedUntilt Ω p b n : Ω), by
    rw [LocalGeometricFontaine.mem_integerRing, norm_div]
    exact (div_le_one₀ (norm_pos_iff.mpr (shiftedUntilt_ne_zero Ω p b hb n))).mpr
      (shiftedUntilt_norm_le Ω p a b hab n)⟩

theorem quotientLift_mul (a b : GeometricTiltField.Source Ω p) (hb : b ≠ 0) (hab : ‖a‖ ≤ ‖b‖)
    (n : ℕ) : shiftedUntilt Ω p b n * quotientLift Ω p a b hb hab n = shiftedUntilt Ω p a n := by
  apply Subtype.ext
  exact mul_div_cancel₀ _ (shiftedUntilt_ne_zero Ω p b hb n)

variable [IsAlgClosed Ω]

/-- Move a compatible-root lift of the actual quotient forward n Frobenius steps. -/
def approximation (a b : GeometricTiltField.Source Ω p) (hb : b ≠ 0) (hab : ‖a‖ ≤ ‖b‖)
    (n : ℕ) : GeometricTiltField.Source Ω p :=
  (frobenius (GeometricTiltField.Source Ω p) p)^[n]
    (GeometricTiltSharp.rootLift Ω p (quotientLift Ω p a b hb hab n))

theorem approximation_coeff (a b : GeometricTiltField.Source Ω p) (hb : b ≠ 0) (hab : ‖a‖ ≤ ‖b‖)
    (n : ℕ) : PreTilt.coeff n (approximation Ω p a b hb hab n) =
      Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)})
        (quotientLift Ω p a b hb hab n) := by
  rw [approximation]
  have h := PreTilt.coeff_iterate_frobenius 0 n
    (GeometricTiltSharp.rootLift Ω p (quotientLift Ω p a b hb hab n))
  rw [Nat.zero_add] at h
  rw [h, ← PreTilt.mk_untilt_eq_coeff_zero, GeometricTiltSharp.untilt_rootLift]

theorem approximation_error_coeff (a b : GeometricTiltField.Source Ω p) (hb : b ≠ 0)
    (hab : ‖a‖ ≤ ‖b‖) (n : ℕ) : PreTilt.coeff n (a - b * approximation Ω p a b hb hab n) = 0 := by
  rw [map_sub, map_mul, approximation_coeff, sub_eq_zero]
  rw [← shiftedUntilt_reduction Ω p a n, ← shiftedUntilt_reduction Ω p b n, ← map_mul,
    quotientLift_mul]

theorem approximation_error_norm (a b : GeometricTiltField.Source Ω p) (hb : b ≠ 0)
    (hab : ‖a‖ ≤ ‖b‖) (n : ℕ) :
    ‖a - b * approximation Ω p a b hb hab n‖ ≤ ‖(p : Ω)‖ ^ p ^ n :=
  (GeometricPreTiltCompleteness.coeff_eq_zero_iff Ω p _ n).mp
    (approximation_error_coeff Ω p a b hb hab n)

end
end JoshiTeich.Act1Scene1.GeometricPreTiltDivision
