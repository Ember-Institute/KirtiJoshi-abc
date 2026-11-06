import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusSource

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-GENERIC-COMPARISON
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the original
Witt Frobenius on the standard bounded localization.
fidelity: identifies the generic forward localization Frobenius with the
full forward function of the existing standard Frobenius equivalence, using
the localization uniqueness theorem and the original inclusion law.
Every declaration depends only on p and its primality instance. The original
standard carriers, functions and operation instances are retained.
Original proof; no reference implementation copied.
boundary: Scene1/Derived; actual-to-standard Frobenius commutation and the
paper B, period and BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius

noncomputable section
variable (p : ℕ) [Fact p.Prime]

theorem genericHom_eq_frobeniusEquiv :
    (WittPrimeTeichFrobenius.hom p (PadicBoundedWittLocalization.contraction p) :
      PadicBoundedWittLocalization.Ring p → PadicBoundedWittLocalization.Ring p) =
      (frobeniusEquiv p :
        PadicBoundedWittLocalization.Ring p → PadicBoundedWittLocalization.Ring p) := by
  have h := WittPrimeTeichFrobenius.hom_unique p
    (PadicBoundedWittLocalization.contraction p) (frobenius p)
    (frobenius_inclusion_witt p)
  rw [frobeniusEquiv_eq_frobenius p]
  funext x
  exact (RingHom.congr_fun h x).symm

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius
