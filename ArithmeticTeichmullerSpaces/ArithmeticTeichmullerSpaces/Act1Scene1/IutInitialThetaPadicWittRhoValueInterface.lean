import ArithmeticTeichmullerSpaces.Act1Scene1.WittValuePresentationComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoValue
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoValue

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-VALUE-INTERFACE
source: Joshi II `se:ff-rings`, Away presentations of the original bounded
Witt carriers and their original rho values.
fidelity: fixes the native localization maps, presentation relation and value
functions before consuming separately proved quotient formulas. The inverse
law is supplied by the original choice equivalence. The two presentation
formulas and quotient power law remain explicit parameters for the actual
consumer to supply.
Original proof; Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison

open JoshiTeich.Prologue
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeValueInterface : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

private theorem choicePresentationExists
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w
      (InitialThetaPadicBoundedWittComparison.contraction D w)) :
    ∃ (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w),
      x * algebraMap _ _
          (InitialThetaWittLocalizationChoice.choiceDenominator D w
            (InitialThetaPadicBoundedWittComparison.contraction D w)) ^ m =
        algebraMap _ _ a :=
  IsLocalization.Away.surj
    (InitialThetaWittLocalizationChoice.choiceDenominator D w
      (InitialThetaPadicBoundedWittComparison.contraction D w)) x

theorem presentation_value_transfer
    {actualQuotient standardQuotient :
      ℝ≥0∞ → InitialThetaTiltFontaine.Ainf D w → ℕ → ℝ≥0∞}
    (hactual : ∀ (ρ : ℝ≥0∞), ρ ≠ 0 → ρ ≠ ⊤ →
      ∀ (x : InitialThetaWittLocalizationChoice.ChoiceRing D w
          (InitialThetaPadicBoundedWittComparison.contraction D w))
        (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w),
        x * algebraMap _ _
            (InitialThetaWittLocalizationChoice.choiceDenominator D w
              (InitialThetaPadicBoundedWittComparison.contraction D w)) ^ m =
          algebraMap _ _ a →
        InitialThetaWittRhoValue.value D w ρ
            (InitialThetaWittLocalizationChoice.toCanonical D w
              (InitialThetaPadicBoundedWittComparison.contraction D w)
              (InitialThetaPadicBoundedWittComparison.contraction_ne_zero D w) x) =
          actualQuotient ρ a m)
    (hstandard : ∀ (ρ : ℝ≥0∞), ρ ≠ 0 → ρ ≠ ⊤ →
      ∀ (x : InitialThetaWittLocalizationChoice.ChoiceRing D w
          (InitialThetaPadicBoundedWittComparison.contraction D w))
        (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w),
        x * algebraMap _ _
            (InitialThetaWittLocalizationChoice.choiceDenominator D w
              (InitialThetaPadicBoundedWittComparison.contraction D w)) ^ m =
          algebraMap _ _ a →
        PadicWittRhoValue.value (Arithmetic.residueChar w.1) ρ
            (InitialThetaPadicBoundedWittComparison.choiceStandardFun D w x) =
          standardQuotient ρ a m)
    (hquotient : ∀ (ρ : ℝ≥0∞) (a : InitialThetaTiltFontaine.Ainf D w) (m : ℕ),
      standardQuotient ρ a m ^ Arithmetic.localDeg w.1 =
        actualQuotient (ρ ^ Arithmetic.localDeg w.1) a m) :
    ∀ (ρ : ℝ≥0∞), ρ ≠ 0 → ρ ≠ ⊤ →
      ∀ x : InitialThetaBoundedWittLocalization.Ring D w,
        PadicWittRhoValue.value (Arithmetic.residueChar w.1) ρ
            (InitialThetaPadicBoundedWittComparison.ringEquiv D w x) ^
            Arithmetic.localDeg w.1 =
          InitialThetaWittRhoValue.value D w (ρ ^ Arithmetic.localDeg w.1) x := by
  intro ρ hρ0 hρtop x
  exact WittValuePresentationComparison.of_presentation
    (InitialThetaWittLocalizationChoice.toCanonical D w
      (InitialThetaPadicBoundedWittComparison.contraction D w)
      (InitialThetaPadicBoundedWittComparison.contraction_ne_zero D w))
    (InitialThetaWittLocalizationChoice.fromCanonical D w
      (InitialThetaPadicBoundedWittComparison.contraction D w)
      (InitialThetaPadicBoundedWittComparison.contraction_norm_lt_one D w))
    (InitialThetaPadicBoundedWittComparison.choiceStandardFun D w)
    (InitialThetaWittRhoValue.value D w)
    (PadicWittRhoValue.value (Arithmetic.residueChar w.1))
    _ (Arithmetic.localDeg w.1)
    (choicePresentationExists D w)
    (InitialThetaPadicBoundedWittComparison.choiceEquiv D w).apply_symm_apply
    hactual hstandard hquotient ρ hρ0 hρtop x

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
