import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusCachedPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusNativeFunction

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-NATIVE-PRESENTATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on the original bounded Witt denominator presentations.
fidelity: records the proved cached presentation law for the original
standard Frobenius through its native ordinary function. The function has
the original bounded Witt ring explicitly as both source and target and is
definitionally the same original Frobenius. The raw coefficient field and
normed coefficient field match the cached relation and Away quotient law.
The original carrier, denominator and transformed numerator are retained.
All declarations depend only on p and its primality instance. No new map
or comparison assumption is introduced.
Original proof; no reference implementation copied. Prologue R5 retained.
boundary: Scene1/Derived; standard-side native presentation law only.
Actual-to-standard commutation, completion and the paper B, period and BK
identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.NativePresentation

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

local instance rawCoefficientFieldNativePresentation : Field (PadicTiltField.Carrier p) :=
  FractionRing.field (PadicTiltField.Source p)
local instance normedCoefficientFieldNativePresentation :
    NormedField (PadicTiltField.Carrier p) :=
  PadicTiltField.carrierNormedField p
local instance rawIntegerCharPNativePresentation : CharP (PadicTiltField.Integers p) p :=
  rawIntegerCharP p

theorem away_frobenius_presentation
    (x : PadicBoundedWittLocalization.Ring p) (m : ℕ)
    (a : PadicBoundedWittLocalization.Ainf p)
    (hx : PadicWittAwayPresentationRelation.relation p x m a) :
    PadicWittAwayPresentationRelation.relation p
      (NativeFunction.frobeniusFun p x) (p * m)
      (WittFrobeniusPresentation.transform p m a) :=
  CachedPresentation.away_frobenius_presentation p x m a hx

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.NativePresentation
