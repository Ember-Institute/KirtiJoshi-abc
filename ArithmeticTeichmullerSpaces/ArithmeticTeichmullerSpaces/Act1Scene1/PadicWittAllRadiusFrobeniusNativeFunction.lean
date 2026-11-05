import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusFrobenius

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-ALL-RADIUS-FROBENIUS-NATIVE-FUNCTION
source: Joshi II `se:ff-rings`, native ordinary-function form of the
standard all-radius Frobenius.
fidelity: exposes the existing standard all-radius Frobenius with its
original carrier and no new map or comparison law. The alias is used to
keep concrete actual-to-standard consumers from unfolding the bundled
equivalence in their theorem headers. Original proof; no reference code copied.
boundary: native function identification only; inverse, completion and
paper B/period/BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.PadicWittAllRadiusFrobenius.NativeFunction

noncomputable section
variable (p : ℕ) [Fact p.Prime]

def frobeniusFun (x : PadicWittAllRadiusCompletion.Carrier p) :
    PadicWittAllRadiusCompletion.Carrier p :=
  PadicWittAllRadiusFrobenius.frobeniusEquiv p x

theorem frobeniusEquiv_eq_frobeniusFun
    (x : PadicWittAllRadiusCompletion.Carrier p) :
    PadicWittAllRadiusFrobenius.frobeniusEquiv p x = frobeniusFun p x := rfl

theorem frobeniusEquiv_toFun_eq_frobeniusFun :
    (PadicWittAllRadiusFrobenius.frobeniusEquiv p :
      PadicWittAllRadiusCompletion.Carrier p →
        PadicWittAllRadiusCompletion.Carrier p) = frobeniusFun p := rfl

end
end JoshiTeich.Act1Scene1.PadicWittAllRadiusFrobenius.NativeFunction
