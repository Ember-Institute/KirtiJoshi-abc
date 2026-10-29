import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotRawDegreeAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData

/-!
source-id: JT-SCENE1-INITIAL-THETA-QPILOT-RAW-ACCOUNTING
source: the actual InitialThetaData source constructor for the degree-normalized
bundle and the proved raw/degree finite-sum comparison.
fidelity: consumes the bundle's raw certificate to identify its existing raw
target q-sum with degree times q-pilot absLogQ, without a weighted uniformizer
certificate or a degree-one assumption. The base analytic obligations remain
explicit; this does not construct a complete paper-side Scene1 model.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.Corollary312Scene1DegreeNormalizedQPilotData

open JoshiTeich.Prologue

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem qLogSum_eq_degree_mul_absLogQ
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := K) (O := O) p) :
    Corollary312Data.qLogSum p D.base.target =
      (Module.finrank ℚ K : ℝ) * (D.qPilot p).absLogQ p := by
  rw [Corollary312RawTargetSpecification.qLogSum_eq_rawSourceQLogSum p
    (Corollary312RawTargetSpecification.ofTateQFamily p D.base.qFamily)]
  exact Corollary312QPilotSourceIndexBridge.rawSourceQLogSum_eq_degree_mul_absLogQ
    p D.source.orderCompatibility D.rawNormalization D.base.ell_prime.pos
    (D.sourceIndexBridge p)

/-- Degree-normalized presentation of the raw target q-sum. -/
theorem qLogSum_div_degree_eq_absLogQ
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := K) (O := O) p) :
    Corollary312Data.qLogSum p D.base.target / (Module.finrank ℚ K : ℝ) =
      (D.qPilot p).absLogQ p := by
  have hDegree : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    ne_of_gt Arithmetic.finrank_pos
  rw [D.qLogSum_eq_degree_mul_absLogQ p]
  field_simp

/-! The normalized raw target and the grouped normalized source sum share one
    bundle-level equality. -/
theorem qLogSum_div_degree_eq_degreeNormalizedSourceQLogSum
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := K) (O := O) p) :
    Corollary312Data.qLogSum p D.base.target / (Module.finrank ℚ K : ℝ) =
      Corollary312DegreeNormalizedSourceQLogSum p D.base.target
        D.base.qFamily.grouping := by
  calc
    Corollary312Data.qLogSum p D.base.target / (Module.finrank ℚ K : ℝ) =
        (D.qPilot p).absLogQ p := D.qLogSum_div_degree_eq_absLogQ p
    _ = Corollary312DegreeNormalizedSourceQLogSum p D.base.target
        D.base.qFamily.grouping := D.absLogQ_eq_degreeNormalizedSourceQLogSum p

theorem qFactorProduct_eq_exp_neg_qLogSum_div_degree
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := K) (O := O) p) :
    degreeNormalizedSourceQFactorProduct p D.base.target (D.qPilot p) =
      Real.exp (-(Corollary312Data.qLogSum p D.base.target /
        (Module.finrank ℚ K : ℝ))) := by
  have hProduct := D.qFactorProduct_eq_exp_neg_degreeNormalizedSourceQLogSum p
  have hSum := D.qLogSum_div_degree_eq_degreeNormalizedSourceQLogSum p
  rw [hProduct, hSum]

/-- Exact q-pilot presentation of the existing raw target, with its degree
coefficient retained. This equivalence does not prove the volume estimate. -/
theorem corollary312_iff_degreeScaledQPilot
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := K) (O := O) p) :
    Corollary312 p D.base.target ↔
      -(1 / (D.base.target.ellStar : ℝ)) * |Real.log D.base.target.thetaVolume| ≥
        -((Module.finrank ℚ K : ℝ) * (D.qPilot p).absLogQ p) := by
  rw [Corollary312, D.qLogSum_eq_degree_mul_absLogQ p]

end JoshiTeich.Act1Scene1.Corollary312Scene1DegreeNormalizedQPilotData
