import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoFrobenius

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-NATIVE-RING-HOM
source: Joshi II `se:ff-rings`, Frobenius as the original localization ring hom.
fidelity: caches the existing standard Frobenius equivalence as its original
ring-hom projection. This moves only elaboration of the p-only target map;
the carrier, equivalence and operation dictionaries are unchanged.
Original proof; no reference implementation copied. Prologue R5 retained.
boundary: standard bounded map wrapper only; actual comparison, completion and
paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.NativeRingHom

noncomputable section
variable (p : ℕ) [Fact p.Prime]

variable {A : Type*} [Semiring A]

def frobeniusRingHom :
    PadicBoundedWittLocalization.Ring p →+*
      PadicBoundedWittLocalization.Ring p :=
  (PadicWittRhoFrobenius.frobeniusEquiv p).toRingHom

theorem frobeniusRingHom_apply (x : PadicBoundedWittLocalization.Ring p) :
    frobeniusRingHom p x = PadicWittRhoFrobenius.frobeniusEquiv p x := rfl

def afterEquiv (E : A ≃+* PadicBoundedWittLocalization.Ring p) :
    A →+* PadicBoundedWittLocalization.Ring p :=
  (frobeniusRingHom p).comp E.toRingHom

theorem afterEquiv_apply (E : A ≃+* PadicBoundedWittLocalization.Ring p)
    (x : A) :
    afterEquiv p E x = PadicWittRhoFrobenius.frobeniusEquiv p (E x) := rfl

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.NativeRingHom
