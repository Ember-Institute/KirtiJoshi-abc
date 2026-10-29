import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionBaseWeightedProductDefect
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedBaseSupportCoverage
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperRootNormProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-SELECTED-PRODUCT-BRIDGE
source: the actual torsion/base section product defect, the selected base
support coverage equivalence, and the selected root norm product.
fidelity: under an explicit full-support coverage hypothesis, transports the
arbitrary actual base section product to the selected actual q-root product and
therefore exposes the strict weighted torsion product gap on that carrier.
The coverage hypothesis remains an input; this is not a construction of the
paper `L'` carrier or a proof of the coverage condition.
boundary: Scene1/Derived. Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue NumberField
open scoped BigOperators
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem iutInitialThetaTorsionBaseSectionPaperRootProduct_eq_actualSelectedPaperRootNormProduct_of_fullSupport
    (hCoverage : ∀ w : NumberField.FinitePlace D.F,
      w ∈ IutOddMultiplicativeSupport D →
        iutInitialThetaSectionBasePlace D
            (iutPlaceUnder (F :=
              ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
              (Kt := D.F) w) = w) :
    iutInitialThetaTorsionBaseSectionPaperRootProduct D =
      actualSelectedPaperRootNormProduct D := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let S := {s : R.badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let T := {b : NumberField.FinitePlace D.F //
    b ∈ iutInitialThetaOddSupportSelectedBasePlaces D}
  let _ : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  let _ : Fintype T :=
    (iutInitialThetaOddSupportSelectedBasePlaces_finite D).fintype
  let hSupport : iutInitialThetaOddSupportSelectedBasePlaces D =
      IutOddMultiplicativeSupport D :=
    (iutInitialThetaOddSupportSelectedBasePlaces_eq_fullSupport_iff D).mpr
      hCoverage
  let eSelected := iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv D
  let eBase : T ≃ B.badFinset :=
    { toFun := fun b =>
        ⟨b.1, (Set.ext_iff.mp B.badFinset_spec b.1).mpr (by
          have hbSupport : b.1 ∈ IutOddMultiplicativeSupport D := by
            simpa [hSupport] using b.2
          exact hbSupport)⟩
      invFun := fun w =>
        ⟨w.1, by
          have hwSupport : w.1 ∈ IutOddMultiplicativeSupport D := by
            have hwB := (Set.ext_iff.mp B.badFinset_spec w.1).mp w.2
            exact hwB
          simpa [hSupport] using hwSupport⟩
      left_inv := by
        intro b
        rfl
      right_inv := by
        intro w
        rfl }
  let e : S ≃ B.badFinset := eSelected.trans eBase
  have hbase (s : S) :
      R.basePlace (iutInitialThetaTorsionBaseSection D (e s)) = R.basePlace s.1 := by
    have hsection := iutInitialThetaTorsionBaseSection_basePlace D (e s)
    exact hsection.trans (by rfl)
  unfold iutInitialThetaTorsionBaseSectionPaperRootProduct
  unfold actualSelectedPaperRootNormProduct
  calc
    (∏ b : B.badFinset,
        actualPaperRootNorm D (iutInitialThetaTorsionBaseSection D b)) =
        ∏ s : S,
          actualPaperRootNorm D (iutInitialThetaTorsionBaseSection D (e s)) := by
      simpa using (e.prod_comp (fun b =>
        actualPaperRootNorm D (iutInitialThetaTorsionBaseSection D b))).symm
    _ = ∏ s : S, actualPaperRootNorm D s.1 := by
      apply Finset.prod_congr rfl
      intro s hs
      exact actualPaperRootNorm_eq_of_same_basePlace D
        (iutInitialThetaTorsionBaseSection D (e s)) s.1 (hbase s)

theorem iutInitialThetaTorsionWeightedPaperRootProduct_gt_actualSelectedPaperRootNormProduct_of_fullSupport
    (hCoverage : ∀ w : NumberField.FinitePlace D.F,
      w ∈ IutOddMultiplicativeSupport D →
        iutInitialThetaSectionBasePlace D
            (iutPlaceUnder (F :=
              ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
              (Kt := D.F) w) = w) :
    actualSelectedPaperRootNormProduct D <
      iutInitialThetaTorsionWeightedPaperRootProduct D := by
  rw [← iutInitialThetaTorsionBaseSectionPaperRootProduct_eq_actualSelectedPaperRootNormProduct_of_fullSupport
    D hCoverage]
  exact iutInitialThetaTorsionWeightedPaperRootProduct_gt_baseSectionProduct D

end
end JoshiTeich.Act1Scene1
