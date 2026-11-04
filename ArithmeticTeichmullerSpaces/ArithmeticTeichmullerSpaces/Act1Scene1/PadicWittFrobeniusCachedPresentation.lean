import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusRawPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAwayPresentationRelation

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-CACHED-PRESENTATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on the original bounded Witt denominator presentations.
fidelity: states the proved raw standard Frobenius presentation law through
the cached original Away presentation relation. The raw coefficient field
and normed coefficient field match the original Away quotient value law.
The original Frobenius function, carrier, denominator and transformed
numerator are retained. Every declaration depends only on p and its
primality instance; no new map or comparison assumption is introduced.
Original proof; no reference implementation copied. Prologue R5 retained.
boundary: Scene1/Derived; standard-side cached presentation law only.
Actual-to-standard commutation, completion and the paper B, period and BK
identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.CachedPresentation

noncomputable section
variable (p : ℕ) [Fact p.Prime]

private theorem rawIntegerCharP :
    (letI : Field (PadicTiltField.Carrier p) := FractionRing.field (PadicTiltField.Source p)
     letI : NormedField (PadicTiltField.Carrier p) := PadicTiltField.carrierNormedField p
     CharP (PadicTiltField.Integers p) p) := by
  have hcast : ∀ n : ℕ, (n : PadicTiltField.Integers p) = 0 ↔ p ∣ n :=
    CharP.cast_eq_zero_iff (PadicTiltField.Integers p) p
  letI : Field (PadicTiltField.Carrier p) := FractionRing.field (PadicTiltField.Source p)
  letI : NormedField (PadicTiltField.Carrier p) := PadicTiltField.carrierNormedField p
  exact ⟨hcast⟩

local instance rawCoefficientFieldCachedPresentation : Field (PadicTiltField.Carrier p) :=
  FractionRing.field (PadicTiltField.Source p)
local instance normedCoefficientFieldCachedPresentation :
    NormedField (PadicTiltField.Carrier p) :=
  PadicTiltField.carrierNormedField p
local instance rawIntegerCharPCachedPresentation : CharP (PadicTiltField.Integers p) p :=
  rawIntegerCharP p

theorem away_frobenius_presentation
    (x : PadicBoundedWittLocalization.Ring p) (m : ℕ)
    (a : PadicBoundedWittLocalization.Ainf p)
    (hx : PadicWittAwayPresentationRelation.relation p x m a) :
    PadicWittAwayPresentationRelation.relation p
      (PadicWittRhoFrobenius.frobeniusEquiv p x) (p * m)
      (WittFrobeniusPresentation.transform p m a) :=
  RawPresentation.away_frobenius_presentation p x m a hx

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.CachedPresentation
