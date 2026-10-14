import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRelativeQRootProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperRootNormProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-PAPER-ROOT-PRODUCT-BOUND
source: actual selected representative ramification gap and Joshi III
multiplicative root estimate (3617--3631).
fidelity: derives a strict product comparison from the proved strict
negative-log accounting. It uses the actual section-selected carrier;
no equality of normalized q-pilot and unweighted paper sum is assumed,
and no paper V_p^oss carrier or weighted theta volume is identified.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem actualSelectedPaperRootNormProduct_lt_normalizedVBadRootProduct :
    actualSelectedPaperRootNormProduct D < iutInitialThetaNormalizedVBadRelativeQRootProduct D := by
  have h := iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum D
  rw [← iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D,
    ← actualSelectedPaperRootNormProduct_negLog_eq_paperSum D] at h
  exact (Real.log_lt_log_iff (actualSelectedPaperRootNormProduct_mem_Ioo D).1
    (iutInitialThetaNormalizedVBadRelativeQRootProduct_pos D)).mp (neg_lt_neg_iff.mp h)

theorem actualSelectedPaperRootNormProduct_pow_lt_normalizedVBadRootProduct_pow
    (n : ℕ) (hn : 0 < n) :
    actualSelectedPaperRootNormProduct D ^ n <
      iutInitialThetaNormalizedVBadRelativeQRootProduct D ^ n :=
  pow_lt_pow_left₀ (actualSelectedPaperRootNormProduct_lt_normalizedVBadRootProduct D)
    (actualSelectedPaperRootNormProduct_mem_Ioo D).1.le hn.ne'

end
end JoshiTeich.Act1Scene1
