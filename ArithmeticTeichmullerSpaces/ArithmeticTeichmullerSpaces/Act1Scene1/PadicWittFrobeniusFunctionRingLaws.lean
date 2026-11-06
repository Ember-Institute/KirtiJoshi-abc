import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusSource

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-FUNCTION-RING-LAWS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the original
Frobenius on the standard bounded Witt localization.
fidelity: records the existing Frobenius equivalence's preservation of one
and multiplication with the exact inferred operation dictionaries. Every
declaration depends only on p and its primality instance. The original
functions and carriers are retained; no new map or source assumption is
introduced.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; these operation laws do not establish Frobenius
comparison or the paper B, period or BK identities.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius

noncomputable section
variable (p : ℕ) [Fact p.Prime]

set_option linter.defProp false in
def frobeniusEquiv_map_one := (frobeniusEquiv p).map_one

set_option linter.defProp false in
def frobeniusEquiv_map_mul := (frobeniusEquiv p).map_mul

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius
