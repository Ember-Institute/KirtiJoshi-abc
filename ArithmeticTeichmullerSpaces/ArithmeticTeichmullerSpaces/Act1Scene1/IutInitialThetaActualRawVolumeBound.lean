import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLinkSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadHullLogCost
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting

/-!
source-id: JT-SCENE1-ACTUAL-RAW-VOLUME-BOUND
source: actual Tate completion norm/order, finite arithmetic-degree sum, and
ordinary-log hull Haar identity; Joshi III 3495--3557 and 3617--3645.
fidelity: derives raw q-sum accounting and the actual ordinary-log hull bound
from InitialThetaData alone. No Scene1Input, theta/period laws, perfectoid
bridge, volume identity or target inequality is a theorem parameter. These
numeric results do not identify the model with paper theta/BK/untilt loci.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaRawQ
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev Index := ↥(IutBaseQPilotSource.ofInitialThetaData D).badFinset

def factor (w : Index D) : ℝ :=
  (iutInitialThetaTateParameterData D).norm w.1 ^ (1 / (2 * (D.prime.ℓ : ℝ)))

def logTerm (w : Index D) : ℝ := -Real.log (factor D w)
def logSum : ℝ := ∑ w : Index D, logTerm D w
def product : ℝ := ∏ w : Index D, factor D w

theorem factor_pos (w : Index D) : 0 < factor D w :=
  Real.rpow_pos_of_pos ((iutInitialThetaTateParameterData_laws D).norm_pos w.1 w.2) _

theorem product_pos : 0 < product D :=
  Finset.prod_pos fun w _ => factor_pos D w

/-- The local factor uses the actual completion norm, including residue degree. -/
theorem logTerm_eq_order_term (w : Index D) :
    logTerm D w = (Arithmetic.inertDeg w.1 : ℝ) *
      ((IutBaseQPilotSource.ofInitialThetaData D).qOrder w : ℝ) *
      Real.log (Arithmetic.residueChar w.1) / (2 * (D.prime.ℓ : ℝ)) := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  have hparameter : (iutInitialThetaTateParameterData D).parameter w.1 =
      B.tateParameter w := by
    change (if hw : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
      ((D.prime.tate w.1 hw).q : w.1.maximalIdeal.adicCompletion D.F) else 0) = _
    have hbad : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := B.mem_badPlaces w
    rw [dite_eq_left hbad]
    rfl
  unfold logTerm factor
  rw [(iutInitialThetaTateParameterData_laws D).norm_eq w.1 w.2, hparameter,
    Real.log_rpow (norm_pos_iff.mpr (B.tateParameter_ne_zero w)),
    Arithmetic.completionNorm_eq_residueChar_pow_neg_qOrder w.1 (B.tateParameter w)
      (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w),
    Real.log_zpow, Real.log_pow]
  push_cast
  change -((1 / (2 * (D.prime.ℓ : ℝ))) *
    (-(B.qOrder w : ℝ) *
      ((Arithmetic.inertDeg w.1 : ℝ) * Real.log (Arithmetic.residueChar w.1)))) = _
  ring

theorem logSum_eq_degree_mul_reference :
    logSum D = (Module.finrank ℚ D.F : ℝ) *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  change (∑ w : B.badFinset, logTerm D w) = (Module.finrank ℚ D.F : ℝ) *
    ((∑ w : B.badFinset, Arithmetic.qPilotWeight w.1 *
      (D.prime.qOrder w.1 (B.mem_badPlaces w) : ℝ) *
      Real.log (Arithmetic.residueChar w.1)) / (2 * (D.prime.ℓ : ℝ)))
  rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  rw [logTerm_eq_order_term D w, IutCompletionTateValuation.base_qOrder_eq_initialTheta_qOrder]
  unfold Arithmetic.qPilotWeight
  have hdegree : (Module.finrank ℚ D.F : ℝ) ≠ 0 := ne_of_gt Arithmetic.finrank_pos
  field_simp [hdegree]

theorem reference_le_logSum :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
      (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤ logSum D := by
  rw [logSum_eq_degree_mul_reference D]
  have hdegree : (1 : ℝ) ≤ Module.finrank ℚ D.F := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Module.finrank_pos : 0 < Module.finrank ℚ D.F))
  exact le_mul_of_one_le_left (iutInitialThetaReferenceAbsLogQ_pos D).le hdegree

theorem log_product_eq_neg_logSum : Real.log (product D) = -logSum D := by
  rw [product, Real.log_prod (fun w _ => (factor_pos D w).ne')]
  simp only [logSum, logTerm, Finset.sum_neg_distrib, neg_neg]

variable (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)

/-- A numerical Haar lower bound independent of the legacy analytic interface. -/
theorem product_pow_le_actualVolume :
    product D ^ n ≤ VBadThetaLogCollation.volume D n σ hσ := by
  have hlog := VBadThetaLogCollation.negLog_volume_eq_mul_referenceAbsLogQ D n σ hσ
  have hvolume : VBadThetaLogCollation.volume D n σ hσ =
      Real.exp (-((n : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D))) := by
    rw [← hlog, neg_neg]
    exact (Real.exp_log (VBadThetaLogCollation.volume_pos D n σ hσ)).symm
  have hproduct : product D ^ n = Real.exp (-((n : ℝ) * logSum D)) := by
    rw [← Real.exp_log (pow_pos (product_pos D) n), Real.log_pow,
      log_product_eq_neg_logSum, mul_neg]
  rw [hproduct, hvolume]
  exact Real.exp_le_exp.mpr
    (neg_le_neg (mul_le_mul_of_nonneg_left (reference_le_logSum D) (Nat.cast_nonneg n)))

theorem negAverageAbsLog_actualVolume_ge_neg_logSum (hn : 0 < n) :
    -(1 / (n : ℝ)) * |Real.log (VBadThetaLogCollation.volume D n σ hσ)| ≥
      -logSum D := by
  rw [VBadThetaLogCollation.negAverageAbsLog_volume_eq_referenceLhs D n σ hσ hn]
  exact neg_le_neg (reference_le_logSum D)

end
end JoshiTeich.Act1Scene1.InitialThetaRawQ

namespace JoshiTeich.Act1Scene1.CanonicalActualHull
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def length : ℕ := (D.prime.ℓ - 1) / 2

theorem length_pos : 0 < length D := by
  have h := D.prime.five_le
  unfold length
  omega

def tuple (v : iutInitialThetaVBadModuliFinset D) (_ : Fin (length D)) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  VBadSelectedPaper.sourceAt D v

theorem tuple_liesOver (v : iutInitialThetaVBadModuliFinset D) (i : Fin (length D)) :
    Ideal.LiesOver (tuple D v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal :=
  VBadSelectedPaper.sourceAt_liesOver D v

abbrev collation := VBadThetaLogCollation.collation D (length D) (tuple D) (tuple_liesOver D)
abbrev cost := VBadThetaHullLogCost.cost D (length D) (tuple D) (tuple_liesOver D) (collation D)
abbrev hullVolume := VBadThetaLogCollation.volume D (length D) (tuple D) (tuple_liesOver D)

/-- The actual raw bound needs only InitialThetaData. -/
theorem raw_volume_bound :
    -(1 / (length D : ℝ)) * |Real.log (hullVolume D)| ≥ -InitialThetaRawQ.logSum D :=
  InitialThetaRawQ.negAverageAbsLog_actualVolume_ge_neg_logSum
    D (length D) (tuple D) (tuple_liesOver D) (length_pos D)

end
end JoshiTeich.Act1Scene1.CanonicalActualHull
