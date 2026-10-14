import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRelativeQRootProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-ROOT-PRODUCT-CONTRACTING
source: actual nonempty VBad and contracting relative q-root factors.
fidelity: proves the normalized VBad product is strictly contracting and
the actual reference absLogQ is positive, without extra nonempty input.
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

theorem iutInitialThetaVBadRelativeQRootProduct_lt_one :
    iutInitialThetaVBadRelativeQRootProduct D < 1 := by
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  let w : iutInitialThetaVBadModuliFinset D :=
    ⟨v, (mem_iutInitialThetaVBadModuliFinset_iff D v).mpr hv⟩
  have h := Finset.prod_lt_prod_of_nonempty₀
    (s := Finset.univ) (g := fun _ : iutInitialThetaVBadModuliFinset D => (1 : ℝ))
    (fun x _ => (iutInitialThetaRelativeQRootFactor_mem_Ioo D (iutInitialThetaVBadModuliAt D x)).1)
    (fun x _ => (iutInitialThetaRelativeQRootFactor_mem_Ioo D (iutInitialThetaVBadModuliAt D x)).2)
    ⟨w, Finset.mem_univ _⟩
  simpa only [iutInitialThetaVBadRelativeQRootProduct, Finset.prod_const_one] using h

theorem iutInitialThetaNormalizedVBadRelativeQRootProduct_lt_one :
    iutInitialThetaNormalizedVBadRelativeQRootProduct D < 1 :=
  Real.rpow_lt_one (iutInitialThetaVBadRelativeQRootProduct_pos D).le
    (iutInitialThetaVBadRelativeQRootProduct_lt_one D)
    (one_div_pos.mpr (Arithmetic.finrank_pos
      (K := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))))

theorem iutInitialThetaReferenceAbsLogQ_pos :
    0 < JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [← iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D]
  exact neg_pos.mpr (Real.log_neg (iutInitialThetaNormalizedVBadRelativeQRootProduct_pos D)
    (iutInitialThetaNormalizedVBadRelativeQRootProduct_lt_one D))

end
end JoshiTeich.Act1Scene1
