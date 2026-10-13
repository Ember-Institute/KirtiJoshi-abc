import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadModuliJAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-RELATIVE-QROOT-PRODUCT
source: actual VBad moduli fibres and actual inverse relative-degree root factors.
fidelity: restricts the numerical root product to exactly actual VBad. After
moduli global-degree normalization its negative log equals the actual reference
q-pilot, and the product equals exp(-absLogQ). No full-support equality, theta
measure or paper carrier/norm/hull identity is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev iutInitialThetaVBadModuliAt (v : iutInitialThetaVBadModuliFinset D) :
    iutInitialThetaOddModSupportFinset D := ⟨v.1, (Finset.mem_filter.mp v.2).1⟩

def iutInitialThetaVBadRelativeQRootProduct : ℝ :=
  ∏ v : iutInitialThetaVBadModuliFinset D,
    iutInitialThetaRelativeQRootFactor D (iutInitialThetaVBadModuliAt D v)

def iutInitialThetaNormalizedVBadRelativeQRootProduct : ℝ :=
  iutInitialThetaVBadRelativeQRootProduct D ^
    (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))

theorem iutInitialThetaVBadRelativeQRootProduct_pos :
    0 < iutInitialThetaVBadRelativeQRootProduct D := by
  unfold iutInitialThetaVBadRelativeQRootProduct
  exact Finset.prod_pos fun v _ =>
    (iutInitialThetaRelativeQRootFactor_mem_Ioo D (iutInitialThetaVBadModuliAt D v)).1

theorem iutInitialThetaNormalizedVBadRelativeQRootProduct_pos :
    0 < iutInitialThetaNormalizedVBadRelativeQRootProduct D :=
  Real.rpow_pos_of_pos (iutInitialThetaVBadRelativeQRootProduct_pos D) _

theorem iutInitialThetaVBadRelativeQRootProduct_negLog_div_eq_referenceAbsLogQ :
    -Real.log (iutInitialThetaVBadRelativeQRootProduct D) /
        Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have href := iutInitialThetaReferenceAbsLogQ_eq_VBadModuliJLogSum D
  rw [Finset.sum_div, ← Finset.sum_coe_sort] at href
  rw [iutInitialThetaVBadRelativeQRootProduct,
    Real.log_prod (fun v _ =>
      (iutInitialThetaRelativeQRootFactor_mem_Ioo D (iutInitialThetaVBadModuliAt D v)).1.ne'),
    ← Finset.sum_neg_distrib, Finset.sum_div, href]
  exact Finset.sum_congr rfl fun v _ =>
    iutInitialThetaRelativeQRootFactor_negLog_div_eq_moduliJLogTerm D (iutInitialThetaVBadModuliAt D v)

theorem iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ :
    -Real.log (iutInitialThetaNormalizedVBadRelativeQRootProduct D) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [iutInitialThetaNormalizedVBadRelativeQRootProduct,
    Real.log_rpow (iutInitialThetaVBadRelativeQRootProduct_pos D)]
  calc
    _ = -Real.log (iutInitialThetaVBadRelativeQRootProduct D) /
        Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) := by ring
    _ = _ := iutInitialThetaVBadRelativeQRootProduct_negLog_div_eq_referenceAbsLogQ D

theorem iutInitialThetaNormalizedVBadRelativeQRootProduct_eq_exp_neg_referenceAbsLogQ :
    iutInitialThetaNormalizedVBadRelativeQRootProduct D =
      Real.exp (-JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D)) := by
  have h := iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D
  calc
    _ = Real.exp (Real.log (iutInitialThetaNormalizedVBadRelativeQRootProduct D)) :=
      (Real.exp_log (iutInitialThetaNormalizedVBadRelativeQRootProduct_pos D)).symm
    _ = _ := by congr 1; linarith

end
end JoshiTeich.Act1Scene1
