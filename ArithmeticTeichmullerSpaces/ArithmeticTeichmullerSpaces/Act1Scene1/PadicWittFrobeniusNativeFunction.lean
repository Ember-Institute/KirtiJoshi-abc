import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoFrobenius

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-NATIVE-FUNCTION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on the original standard bounded Witt localization.
fidelity: records the existing standard Frobenius as an ordinary function
with the original bounded Witt ring explicitly given as both its source
and target. The original forward function is unchanged, as witnessed by
definitional pointwise and full-function equalities. Every declaration
depends only on p and its primality instance. No dictionary coherence or
comparison assumption is introduced; the original carrier is retained.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; native function identification only. Presentation
transport, actual-to-standard commutation, completion and the paper B,
period and BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.NativeFunction

noncomputable section
variable (p : ℕ) [Fact p.Prime]

def frobeniusFun (x : PadicBoundedWittLocalization.Ring p) :
    PadicBoundedWittLocalization.Ring p :=
  PadicWittRhoFrobenius.frobeniusEquiv p x

theorem frobeniusEquiv_eq_frobeniusFun (x : PadicBoundedWittLocalization.Ring p) :
    PadicWittRhoFrobenius.frobeniusEquiv p x = frobeniusFun p x := rfl

theorem frobeniusEquiv_toFun_eq_frobeniusFun :
    (PadicWittRhoFrobenius.frobeniusEquiv p :
      PadicBoundedWittLocalization.Ring p → PadicBoundedWittLocalization.Ring p) =
      frobeniusFun p := rfl

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.NativeFunction
