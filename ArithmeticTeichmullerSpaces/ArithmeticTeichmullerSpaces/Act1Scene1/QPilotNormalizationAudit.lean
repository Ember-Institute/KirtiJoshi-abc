import ArithmeticTeichmullerSpaces.Act1Scene1.QNormDegreeBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotSourceBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-NORMALIZATION-AUDIT
source: raw finite-place completion norm law from
`iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean`;
q-pilot weight `inertDeg / [K : ℚ]` from
`iut`: `refer/iut/Iut/Concrete/ThetaRegion.lean`;
target-side adapter: `QNormDegreeBridge` and `QPilotSourceBridge`.
fidelity: an incompatibility audit for two separately available Scene1
normalization certificates.  It does not add either certificate to
Prologue/Core and does not choose the final Corollary 3.12 q-factor.
boundary: Scene1/Derived

The raw completion norm has logarithm
`inertDeg(w) * log(residueChar(w))`, while the q-pilot source certificate
assigns the same logarithm the coefficient
`inertDeg(w) / [K : ℚ]`.  Since both factors are positive at every finite
place, their simultaneous use forces the global degree to be one.  This is
the audit obstruction that prevents the raw q-pilot adapter from being
treated as a general-number-field source model.
-/

namespace Corollary312QPilotNormalizationAudit

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}

theorem finrank_eq_one_of_raw_and_weighted_normalization
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hWeighted : Corollary312QPilotSourceNormalization p T hOrder Q)
    (w : NumberField.FinitePlace K)
    (hw : w ∈ Q.badFinset) :
    Module.finrank ℚ K = 1 := by
  have hPrime : 1 < (Arithmetic.residueChar w : ℝ) := by
    exact_mod_cast (Arithmetic.residueChar_prime w).one_lt
  have hLog : 0 < Real.log (Arithmetic.residueChar w) :=
    Real.log_pos hPrime
  have hInert : 0 < (Arithmetic.inertDeg w : ℝ) := by
    exact_mod_cast Arithmetic.inertDeg_pos w
  have hRawLog := hRaw.uniformizer_log_eq_residueDegree_log w hw
  have hWeightedLog :=
    hWeighted.uniformizer_log_eq_weighted_residueChar_log w hw
  have hWeight := hRaw.weight_eq_qPilotWeight w
  have hEqual :
      (Arithmetic.inertDeg w : ℝ) * Real.log (Arithmetic.residueChar w) =
        ((Arithmetic.inertDeg w : ℝ) /
          (Module.finrank ℚ K : ℝ)) *
          Real.log (Arithmetic.residueChar w) := by
    calc
      (Arithmetic.inertDeg w : ℝ) * Real.log (Arithmetic.residueChar w) =
          -Real.log (hOrder.uniformizerNorm w) := hRawLog.symm
      _ = Q.weight w * Real.log (Arithmetic.residueChar w) := hWeightedLog
      _ = Arithmetic.qPilotWeight w * Real.log (Arithmetic.residueChar w) := by
        rw [hWeight]
      _ = ((Arithmetic.inertDeg w : ℝ) /
          (Module.finrank ℚ K : ℝ)) *
          Real.log (Arithmetic.residueChar w) := by
        rfl
  have hDegreePos : (0 : ℝ) < Module.finrank ℚ K :=
    Arithmetic.finrank_pos
  have hDegreeNe : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    ne_of_gt hDegreePos
  have hProduct :
      (Arithmetic.inertDeg w : ℝ) * Real.log (Arithmetic.residueChar w) ≠ 0 :=
    ne_of_gt (mul_pos hInert hLog)
  have hEqualMul :
      ((Arithmetic.inertDeg w : ℝ) * Real.log (Arithmetic.residueChar w)) *
          (Module.finrank ℚ K : ℝ) =
        (Arithmetic.inertDeg w : ℝ) * Real.log (Arithmetic.residueChar w) := by
    calc
      ((Arithmetic.inertDeg w : ℝ) * Real.log (Arithmetic.residueChar w)) *
          (Module.finrank ℚ K : ℝ) =
          (((Arithmetic.inertDeg w : ℝ) /
            (Module.finrank ℚ K : ℝ)) *
            Real.log (Arithmetic.residueChar w)) *
              (Module.finrank ℚ K : ℝ) := by rw [hEqual]
      _ = (Arithmetic.inertDeg w : ℝ) * Real.log (Arithmetic.residueChar w) := by
        field_simp [hDegreeNe]
  have hDegreeOne : (Module.finrank ℚ K : ℝ) = 1 := by
    apply (mul_left_cancel₀ hProduct)
    simpa using hEqualMul
  exact_mod_cast hDegreeOne

end Corollary312QPilotNormalizationAudit

end JoshiTeich.Act1Scene1
