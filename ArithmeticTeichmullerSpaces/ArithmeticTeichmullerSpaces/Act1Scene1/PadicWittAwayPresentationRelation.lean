import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoAwayQuotient

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-AWAY-PRESENTATION-RELATION
source: Joshi II `se:ff-rings`, denominator-power presentations of the
independent standard bounded Witt localization.
fidelity: saves the exact presentation relation with the same raw
coefficient field and normed coefficient field instances as the original
standard Away quotient law. The identity theorem retains a supplied
proof of this relation; uniqueness cancels the original denominator
power, which is a unit. Every declaration depends only on p and its
primality instance. The original inclusion, denominator, carrier and
operations are retained. Original proofs; no reference implementation
copied.
boundary: standard algebraic presentation relation only; concrete map
compatibility, Frobenius commutation, completion and paper B, period and
BK identities remain separate. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittAwayPresentationRelation

noncomputable section
variable (p : ℕ) [Fact p.Prime]

local instance rawCoefficientField : Field (PadicTiltField.Carrier p) :=
  FractionRing.field (PadicTiltField.Source p)
local instance normedCoefficientField : NormedField (PadicTiltField.Carrier p) :=
  PadicTiltField.carrierNormedField p

def relation (x : PadicBoundedWittLocalization.Ring p) (m : ℕ)
    (a : PadicBoundedWittLocalization.Ainf p) : Prop :=
  x * PadicBoundedWittLocalization.inclusion p
      (PadicBoundedWittLocalization.denominator p) ^ m =
    PadicBoundedWittLocalization.inclusion p a

theorem of_relation (x : PadicBoundedWittLocalization.Ring p) (m : ℕ)
    (a : PadicBoundedWittLocalization.Ainf p)
    (hx : relation p x m a) : relation p x m a := hx

theorem unique (x y : PadicBoundedWittLocalization.Ring p) (m : ℕ)
    (a : PadicBoundedWittLocalization.Ainf p)
    (hx : relation p x m a) (hy : relation p y m a) : x = y := by
  have hu : IsUnit
      (PadicBoundedWittLocalization.inclusion p
        (PadicBoundedWittLocalization.denominator p)) :=
    IsLocalization.Away.algebraMap_isUnit (PadicBoundedWittLocalization.denominator p)
  exact (hu.pow m).mul_right_cancel (hx.trans hy.symm)

end
end JoshiTeich.Act1Scene1.PadicWittAwayPresentationRelation
