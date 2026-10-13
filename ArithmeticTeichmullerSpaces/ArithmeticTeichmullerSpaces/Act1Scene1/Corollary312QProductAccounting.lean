import ArithmeticTeichmullerSpaces.Act1Scene1.Corollary312
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
source-id: JT-SCENE1-COR312-QPRODUCT-ACCOUNTING
source: `cor:cor312` q-product shape and the finite procession product.
fidelity: isolates the analytic identity used by the target proof: the log of
the `ellStar`-powered q-product is `ellStar` times the sum of q-factor logs.
The theorem consumes positive q-factors and constructs no q-family, theta
volume, packet map, or paper carrier.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open scoped BigOperators
universe uK
noncomputable section
variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem corollary312_qProduct_pos
    (T : Corollary312Data K O p) (qFactor : T.qIndex → ℝ)
    (hPos : ∀ i, 0 < qFactor i) :
    letI := T.qIndexFintype
    0 < Corollary312Data.qProduct p T qFactor := by
  letI := T.qIndexFintype
  unfold Corollary312Data.qProduct
  exact Finset.prod_pos (fun i hi => pow_pos (hPos i) _)

theorem corollary312_log_qProduct_eq_ellStar_mul_sum_log
    (T : Corollary312Data K O p) (qFactor : T.qIndex → ℝ)
    (hPos : ∀ i, 0 < qFactor i) :
    letI := T.qIndexFintype
    Real.log (Corollary312Data.qProduct p T qFactor) =
      (T.ellStar : ℝ) * ∑ i, Real.log (qFactor i) := by
  letI := T.qIndexFintype
  unfold Corollary312Data.qProduct
  rw [Real.log_prod]
  · simp_rw [Real.log_pow]
    rw [← Finset.mul_sum]
  · intro i hi
    exact pow_ne_zero _ (hPos i).ne'

theorem corollary312_negLog_qProduct_eq_ellStar_mul_sum_negLog
    (T : Corollary312Data K O p) (qFactor : T.qIndex → ℝ)
    (hPos : ∀ i, 0 < qFactor i) :
    letI := T.qIndexFintype;
    (-Real.log (Corollary312Data.qProduct p T qFactor) =
      (T.ellStar : ℝ) * (∑ i, (-Real.log (qFactor i)))) := by
  rw [corollary312_log_qProduct_eq_ellStar_mul_sum_log p T qFactor hPos]
  rw [Finset.sum_neg_distrib]
  ring

end
end JoshiTeich.Act1Scene1
