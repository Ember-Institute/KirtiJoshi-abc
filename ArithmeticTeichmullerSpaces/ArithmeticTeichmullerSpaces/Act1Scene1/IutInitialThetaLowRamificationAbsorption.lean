import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBaseSixthRoot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadOrdinaryLogAbsorption

/-!
source-id: JT-SCENE1-ACTUAL-LOW-RAMIFICATION-ABSORPTION
source: actual base Tate sixth root and VBad source degree bound.
fidelity: at VBad, absolute base ramification at most two suffices to
absorb the ordinary-log correction. The q-order condition is derived
from rational six-torsion. Other places and higher ramification remain
explicit; no BK, untilt or thetaVolume identity is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance lowRamificationPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem relaxed_order_of_base_ramIdx_le_two
    (v : iutInitialThetaOddModSupportFinset D)
    (he : Arithmetic.ramIdx
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
        (FullSupportPaperWeightedHull.selected D v)).1 ≤ 2) :
    sourceThreshold D v ≤ (D.prime.ℓ - 1) * sourceQOrder D v := by
  have hq : 6 ≤ sourceQOrder D v := baseTateParameter_qOrder_ge_six D _
  calc
    sourceThreshold D v ≤ 2 * D.prime.ℓ * 2 := Nat.mul_le_mul_left _ he
    _ ≤ (D.prime.ℓ - 1) * 6 := by have h := D.prime.five_le; omega
    _ ≤ _ := Nat.mul_le_mul_left _ hq

theorem arithmeticAbsorption_on_vbad_of_base_ramIdx_le_two
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad)
    (he : Arithmetic.ramIdx
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
        (FullSupportPaperWeightedHull.selected D v)).1 ≤ 2) :
    arithmeticAbsorption D v :=
  arithmeticAbsorption_on_vbad_of_relaxed_order D v hv
    (relaxed_order_of_base_ramIdx_le_two D v he)

theorem correctedLocalCost_le_paperTerm_on_vbad_of_base_ramIdx_le_two
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad)
    (he : Arithmetic.ramIdx
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
        (FullSupportPaperWeightedHull.selected D v)).1 ≤ 2) :
    correctedLocalCost D v ≤ selectedPaperTerm D v :=
  (correctedLocalCost_le_paperTerm_iff_arithmetic D v).mpr
    (arithmeticAbsorption_on_vbad_of_base_ramIdx_le_two D v hv he)

theorem correctedCost_le_selectedPaperSum_of_low_ramification
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad →
      Arithmetic.ramIdx ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
        (FullSupportPaperWeightedHull.selected D v)).1 ≤ 2)
    (hother : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∉ D.VBad → arithmeticAbsorption D v) :
    FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  correctedCost_le_selectedPaperSum_of_vbad_and_complement D
    (fun v hv => relaxed_order_of_base_ramIdx_le_two D v (he v hv)) hother

variable (n : ℕ) {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw hunit in
theorem ordinary_collation_averageAbsLog_le_selectedPaperSum_of_low_ramification
    (hn : 0 < n)
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad →
      Arithmetic.ramIdx ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
        (FullSupportPaperWeightedHull.selected D v)).1 ≤ 2)
    (hother : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∉ D.VBad → arithmeticAbsorption D v) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  (ordinary_collation_averageAbsLog_le_correctedCost D n C hw hunit hn).trans
    (correctedCost_le_selectedPaperSum_of_low_ramification D he hother)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
