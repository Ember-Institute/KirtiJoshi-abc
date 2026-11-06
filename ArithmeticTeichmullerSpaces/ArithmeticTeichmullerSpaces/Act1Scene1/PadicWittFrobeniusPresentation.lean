import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusSource

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-PRESENTATION
source: Joshi II `se:ff-rings`, denominator presentations under the original
independent standard Witt Frobenius.
fidelity: proves the original standard Frobenius presentation formula and
uniqueness for a fixed original denominator-power presentation. Only p and
primality are required; no actual data or comparison certificate is used.
The original standard map, carrier and denominator are retained. Original
proof; no reference implementation copied.
boundary: standard-side algebraic presentations only; concrete comparison,
completion and paper identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius

noncomputable section
variable (p : ℕ) [Fact p.Prime]

set_option linter.defProp false in
def presentation_unique
    (y z : PadicBoundedWittLocalization.Ring p) (m : ℕ)
    (b : PadicBoundedWittLocalization.Ainf p) :=
  WittFrobeniusPresentation.presentation_unique p
    (PadicBoundedWittLocalization.contraction p) m b (x := y) (y := z)

set_option linter.defProp false in
def away_frobenius_presentation :=
  WittFrobeniusPresentation.map_presentation p
    (PadicBoundedWittLocalization.contraction p)
    (frobeniusEquiv p).toRingHom
    (frobeniusEquiv_inclusion_witt p)

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius
