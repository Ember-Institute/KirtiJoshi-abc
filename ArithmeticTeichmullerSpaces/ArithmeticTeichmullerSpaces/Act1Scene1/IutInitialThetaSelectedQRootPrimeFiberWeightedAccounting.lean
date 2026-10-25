import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootLinkPrimeFiberAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open NumberField
open WithZero
open scoped BigOperators Classical NumberField Valued

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-QROOT-PRIME-FIBER-WEIGHTED-ACCOUNTING
source: the selected q-root source, its base-place q-pilot weight, and the
finite residue-characteristic support of the concrete section/Voss carrier.
fidelity: groups the actual selected q-root weighted ramification/ordp sum
over the same finite rational-prime support used by the Voss carrier.
boundary: this is actual selected-carrier accounting. It does not identify
the carrier with paper `L'` representatives, paper multiplicities, omitted
mass, or a paper theta-volume.
-/

noncomputable def iutInitialThetaSectionVossPrimeSupportFinset
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : Finset ℕ :=
  (iutInitialThetaSectionVossPrimeSupport_finite D).toFinset

noncomputable def iutInitialThetaSelectedQRootPrimeFiberWeightedSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) : ℝ :=
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := iutInitialThetaSelectedQRootLinkSourcePlaceType D
  ∑ s ∈ (Finset.univ : Finset S).filter
      (fun s => Arithmetic.residueChar s.1.1 = p),
    Arithmetic.qPilotWeight (R.basePlace s.1).1 *
      ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
        Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)))

theorem iutInitialThetaSelectedQRootSourcePlaces_qPilotWeighted_sum_eq_primeFiber_sum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let S := iutInitialThetaSelectedQRootLinkSourcePlaceType D
    let P := iutInitialThetaSectionVossPrimeSupportFinset D
    ∑ s : S,
        Arithmetic.qPilotWeight (R.basePlace s.1).1 *
          ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1
              (R.qroot (show R.badFinset from s.1))) =
      ∑ p ∈ P, iutInitialThetaSelectedQRootPrimeFiberWeightedSum D p := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := iutInitialThetaSelectedQRootLinkSourcePlaceType D
  let P := iutInitialThetaSectionVossPrimeSupportFinset D
  let term : S → ℝ := fun s =>
    Arithmetic.qPilotWeight (R.basePlace s.1).1 *
      ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
        Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)))
  have hmaps : ∀ s ∈ (Finset.univ : Finset S),
      Arithmetic.residueChar s.1.1 ∈ P := by
    intro s hs
    have hselected : s.1 ∈
        iutInitialThetaOddSupportSelectedQRootSourcePlaces D := s.2
    have himage : s.1.1 ∈ iutInitialThetaSectionVoss D := by
      have hsource : s.1.1 ∈
          (fun t : R.badFinset => t.1) ''
            iutInitialThetaOddSupportSelectedQRootSourcePlaces D :=
        ⟨s.1, hselected, rfl⟩
      rw [iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionVoss D] at hsource
      exact hsource
    apply (iutInitialThetaSectionVossPrimeSupport_finite D).mem_toFinset.mpr
    exact ⟨s.1.1, himage, rfl⟩
  have hgroup :
      ∑ p ∈ P,
        ∑ s ∈ (Finset.univ : Finset S).filter
          (fun s => Arithmetic.residueChar s.1.1 = p), term s =
      ∑ s : S, term s := by
    exact Finset.sum_fiberwise_of_maps_to hmaps term
  simpa [iutInitialThetaSelectedQRootPrimeFiberWeightedSum, R, S, P, term] using hgroup.symm

end
end JoshiTeich.Act1Scene1
