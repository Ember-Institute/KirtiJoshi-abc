import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoLocalizationPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-ACTUAL-VALUE-PRESENTATION
source: Joshi II `se:ff-rings`, the weighted value of an actual bounded
Witt localization presentation at the transported contraction.
fidelity: specializes the proved actual choice-presentation formula and
retains its full inferred type on the original carriers and norms.
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

local instance selectedPrimeActualValuePresentation : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def actualChoiceQuotient (ρ : ℝ≥0∞)
    (a : InitialThetaTiltFontaine.Ainf D w) (m : ℕ) : ℝ≥0∞ :=
  WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ
      (InitialThetaBoundedWittExpansion.wittInclusion D w a) /
    (ρ * ENNReal.ofReal
      ‖InitialThetaPadicBoundedWittComparison.contraction D w‖) ^ m

theorem actual_choice_value_presentation
    (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w
      (InitialThetaPadicBoundedWittComparison.contraction D w))
    (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w)
    (hx : x * algebraMap _ _
        (InitialThetaWittLocalizationChoice.choiceDenominator D w
          (InitialThetaPadicBoundedWittComparison.contraction D w)) ^ m =
      algebraMap _ _ a) :
    InitialThetaWittRhoValue.value D w ρ
        (InitialThetaWittLocalizationChoice.toCanonical D w
          (InitialThetaPadicBoundedWittComparison.contraction D w)
          (InitialThetaPadicBoundedWittComparison.contraction_ne_zero D w) x) =
      actualChoiceQuotient D w ρ a m := by
  exact InitialThetaWittRhoValue.value_eq_of_choice_presentation D w
    (InitialThetaPadicBoundedWittComparison.contraction D w)
    (InitialThetaPadicBoundedWittComparison.contraction_ne_zero D w)
    (InitialThetaPadicBoundedWittComparison.contraction_norm_lt_one D w)
    ρ hρ0 hρtop x m a hx

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
