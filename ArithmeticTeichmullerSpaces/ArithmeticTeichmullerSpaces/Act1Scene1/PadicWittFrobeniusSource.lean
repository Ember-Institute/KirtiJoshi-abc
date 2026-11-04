import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoFrobenius

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-SOURCE
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the original
Witt Frobenius on the bounded localization source.
fidelity: records the full forward-function equality between the existing
source Frobenius and Witt Frobenius, its existing localization inclusion
law, and the forward function of the existing localization equivalence.
Every declaration depends only on p and its primality instance. The original
functions, rings and inclusions are unchanged.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; actual-to-standard comparison and paper B marking,
period and BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius

noncomputable section
variable (p : ℕ) [Fact p.Prime]

theorem sourceFrobenius_eq_wittFrobenius :
    (sourceFrobenius p : PadicBoundedWittLocalization.Ainf p →
      PadicBoundedWittLocalization.Ainf p) = WittVector.frobenius := rfl

theorem frobenius_inclusion_witt
    (a : PadicBoundedWittLocalization.Ainf p) :
    frobenius p (PadicBoundedWittLocalization.inclusion p a) =
      PadicBoundedWittLocalization.inclusion p (WittVector.frobenius a) :=
  frobenius_inclusion p a

theorem frobeniusEquiv_eq_frobenius :
    (frobeniusEquiv p : PadicBoundedWittLocalization.Ring p →
      PadicBoundedWittLocalization.Ring p) =
      (frobenius p : PadicBoundedWittLocalization.Ring p →
        PadicBoundedWittLocalization.Ring p) := rfl

theorem frobeniusEquiv_inclusion_witt (a : PadicBoundedWittLocalization.Ainf p) :
    frobeniusEquiv p (PadicBoundedWittLocalization.inclusion p a) =
      PadicBoundedWittLocalization.inclusion p (WittVector.frobenius a) := by
  change frobenius p (PadicBoundedWittLocalization.inclusion p a) = _
  exact frobenius_inclusion_witt p a

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius
