import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoLocalizationPresentation

/-!
source-id: JT-SCENE1-PADIC-WITT-RHO-AWAY-QUOTIENT
source: Joshi II `se:ff-rings`, weighted Teichmuller values on a
p-power localization presentation with its contraction denominator.
fidelity: saves the original standard quotient formula on the original
integral Witt carrier, with the original field and norm instances. The
presentation theorem consumes the proved standard localization value law.
Only the prime parameter is used; no new comparison hypothesis or
completed-ring identity is introduced.
Original proof; Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoValue

open scoped ENNReal
noncomputable section

variable (p : ℕ) [Fact p.Prime]

local instance rawCoefficientFieldAwayQuotient : Field (PadicTiltField.Carrier p) :=
  FractionRing.field (PadicTiltField.Source p)
local instance normedCoefficientFieldAwayQuotient :
    NormedField (PadicTiltField.Carrier p) :=
  PadicTiltField.carrierNormedField p

def awayQuotient (ρ : ℝ≥0∞) (a : PadicBoundedWittLocalization.Ainf p)
    (m : ℕ) : ℝ≥0∞ :=
  WittWeightedDigits.value p ρ (PadicBoundedWittExpansion.wittInclusion p a) /
    (ρ * ENNReal.ofReal ‖PadicBoundedWittLocalization.contraction p‖) ^ m

theorem value_eq_awayQuotient
    (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : PadicBoundedWittLocalization.Ring p)
    (m : ℕ) (a : PadicBoundedWittLocalization.Ainf p)
    (hx : x * PadicBoundedWittLocalization.inclusion p
        (PadicBoundedWittLocalization.denominator p) ^ m =
      PadicBoundedWittLocalization.inclusion p a) :
    value p ρ x = awayQuotient p ρ a m :=
  value_eq_of_away_presentation p ρ hρ0 hρtop x m a hx

end
end JoshiTeich.Act1Scene1.PadicWittRhoValue
