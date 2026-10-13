import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootFactor

/-!
source-id: JT-SCENE1-INITIAL-THETA-RELATIVE-QROOT-PRODUCT
source: actual selected relative-degree root factors and complete moduli j-log accounting.
fidelity: computes a presentation-indexed product over all actual odd moduli
representatives. Its degree-normalized negative log equals the full base q-pilot.
No selected-base coverage or new accounting certificate is assumed. The product
is not identified with a presentation-independent tensor measure or theta hull.
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

def iutInitialThetaRelativeQRootProduct : ℝ :=
  ∏ v : iutInitialThetaOddModSupportFinset D, iutInitialThetaRelativeQRootFactor D v

def iutInitialThetaNormalizedRelativeQRootProduct : ℝ :=
  iutInitialThetaRelativeQRootProduct D ^
    (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))

theorem iutInitialThetaRelativeQRootProduct_pos : 0 < iutInitialThetaRelativeQRootProduct D := by
  unfold iutInitialThetaRelativeQRootProduct
  exact Finset.prod_pos fun v _ => (iutInitialThetaRelativeQRootFactor_mem_Ioo D v).1

theorem iutInitialThetaRelativeQRootProduct_negLog_div_eq_fullBaseSum :
    -Real.log (iutInitialThetaRelativeQRootProduct D) /
        Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) =
      iutInitialThetaFullBaseQPilotLogSum D := by
  have hfull := iutInitialThetaFullBaseQPilotLogSum_eq_moduliJLogSum D
  rw [Finset.sum_div, ← Finset.sum_coe_sort] at hfull
  rw [iutInitialThetaRelativeQRootProduct,
    Real.log_prod (fun v _ => (iutInitialThetaRelativeQRootFactor_mem_Ioo D v).1.ne'),
    ← Finset.sum_neg_distrib, Finset.sum_div, hfull]
  exact Finset.sum_congr rfl fun v _ =>
    iutInitialThetaRelativeQRootFactor_negLog_div_eq_moduliJLogTerm D v

theorem iutInitialThetaNormalizedRelativeQRootProduct_negLog_eq_fullBaseSum :
    -Real.log (iutInitialThetaNormalizedRelativeQRootProduct D) =
      iutInitialThetaFullBaseQPilotLogSum D := by
  rw [iutInitialThetaNormalizedRelativeQRootProduct,
    Real.log_rpow (iutInitialThetaRelativeQRootProduct_pos D)]
  calc
    _ = -Real.log (iutInitialThetaRelativeQRootProduct D) /
        Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) := by ring
    _ = _ := iutInitialThetaRelativeQRootProduct_negLog_div_eq_fullBaseSum D

end
end JoshiTeich.Act1Scene1
