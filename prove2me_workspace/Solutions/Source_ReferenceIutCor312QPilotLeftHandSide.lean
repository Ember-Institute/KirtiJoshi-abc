import Solutions.Source_ReferenceIutCor312QPilotNormalization

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

universe u v

open scoped BigOperators

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT) (QI : QPilotInputs D)

/-- The signed q-pilot is the negative of the total negative log of the root norms
across the full torsion-field fibers at `TL.badChars`, with each term divided by
`[D.Kt : ℚ]`. -/
theorem qPilot_lhs_eq_neg_sum_neg_log_norm_qroot :
    (concreteVariantData D LT TL QI).qPilot.lhs =
      -(∑ p ∈ TL.badChars.attach,
        ∑ w : LT.Fiber (.finite (⟨p.1, TL.badChars_prime p.1 p.2⟩ : Nat.Primes)),
          -Real.log ‖TL.qroot (LT.fiberPlace w)‖ / Module.finrank ℚ D.Kt) := by
  let X := concreteVariantData D LT TL QI
  have hsum : ∑ p ∈ TL.badChars, X.logQAt p = X.qPilot.logQ := by
    unfold Corollary312VariantData.logQAt QPilotData.logQ
    exact Finset.sum_fiberwise_of_maps_to
      (fun w _ => TL.bad_residueChar_mem w.1 (X.qPilot.mem_bad w.2)) _
  calc
    X.qPilot.lhs = -(X.qPilot.logQ / (2 * (D.ℓ : ℝ))) := rfl
    _ = -(∑ p ∈ TL.badChars.attach, X.logQAt p.1 / (2 * (D.ℓ : ℝ))) := by
      rw [Finset.sum_attach TL.badChars (fun p => X.logQAt p / (2 * (D.ℓ : ℝ))),
        ← Finset.sum_div, hsum]
    _ = _ := by
      refine congrArg (fun x : ℝ => -x) (Finset.sum_congr rfl fun p _ => ?_)
      exact TowerArithmetic.logQAt_div_two_ell_eq_sum_neg_log_norm_qroot
        (TL := TL) (QI := QI) (⟨p.1, TL.badChars_prime p.1 p.2⟩ : Nat.Primes)

end AbcAdaptation.Reference.Iut.ThetaLocalData
