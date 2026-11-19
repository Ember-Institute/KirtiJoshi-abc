import Solutions.Source_ReferenceIutConcreteLocalEstimate

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.TowerArithmetic

universe u v

open scoped BigOperators

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable {TL : ThetaLocalData D LT} {QI : QPilotInputs D}

/-- The q-pilot contribution at `p`, divided by `2ℓ`, is the negative log of the
adic norms of the chosen Tate roots, summed over the fiber with the absolute degree
as denominator. -/
lemma logQAt_div_two_ell_eq_sum_neg_log_norm_qroot (p : Nat.Primes) :
    (concreteVariantData D LT TL QI).logQAt p / (2 * (D.ℓ : ℝ)) =
      ∑ w : LT.Fiber (.finite p),
        -Real.log ‖TL.qroot (LT.fiberPlace w)‖ / Module.finrank ℚ D.Kt := by
  have hell : (2 * (D.ℓ : ℝ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast D.prime.ℓ_prime.ne_zero)
  rw [logQAt_eq (TL := TL) (QI := QI) p, mul_assoc (2 * (D.ℓ : ℝ)),
    mul_div_cancel_left₀ _ hell, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hweight : LT.weight (.finite p) w = placeWeight D.Kt (LT.fiberPlace w) := by
    simp only [LocalTheory.weight, LT.fiberPlace_spec w]
    rfl
  have hlocal : (localDeg D.Kt (LT.fiberPlace w) : ℝ) ≠ 0 := by
    exact_mod_cast (LT.localDeg_pos (LT.fiberPlace w)).ne'
  have hlog : Real.log (p : ℕ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  have hdegree : (Module.finrank ℚ D.Kt : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ D.Kt).ne'
  rw [hweight, placeWeight, ordp, LT.residueChar_fiberPlace w]
  field_simp [hlocal, hlog, hdegree] <;> ring

end AbcAdaptation.Reference.Iut.TowerArithmetic
