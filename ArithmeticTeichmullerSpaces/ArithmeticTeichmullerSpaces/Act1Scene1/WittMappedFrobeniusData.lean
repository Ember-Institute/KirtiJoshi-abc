import ArithmeticTeichmullerSpaces.Act1Scene1.WittMappedLocalizationComparisonData
import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichFrobenius

/-!
source-id: JT-SCENE1-WITT-MAPPED-FROBENIUS-DATA
source: Joshi II `se:ff-rings`, functorial Frobenius on integral Witt
localizations and the coefficient norm-power comparison.
fidelity: extends the existing norm comparison data with two forward
functions and their proved Frobenius commutation law. The functions are
record fields, so the abstract record type does not expand their concrete
localization constructions. The constructor retains the exact original
norm comparison data and uses the original generic Frobenius homomorphisms
and their naturality theorem. Getter identities preserve their full
functions. No additional comparison certificate, carrier, map, or norm is
introduced. Original proofs; no reference implementation copied.
boundary: generic forward algebraic Frobenius data only; concrete original
Frobenius identities, completion and paper B, period and BK identities
remain separate. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.WittMappedFrobeniusData

noncomputable section

open WittMappedLocalizationComparisonData

structure FrobeniusNormData {A B L M : Type*}
    [CommRing A] [CommRing B] [CommRing L] [CommRing M]
    (f : A → B) (i : A →+* L) (j : B →+* M) (r : A) (s : B)
    (coefficientNormA : A → ℕ → ℝ) (coefficientNormB : B → ℕ → ℝ)
    (d : ℕ) extends NormData f i j r s coefficientNormA coefficientNormB d where
  sourceFrobenius : L → L
  targetFrobenius : M → M
  on_frobenius :
    ∀ x : L, locEquiv (sourceFrobenius x) = targetFrobenius (locEquiv x)

variable (p : ℕ) [Fact p.Prime]
variable {I J : Type*} [CommRing I] [CommRing J] [Norm I] [Norm J]
variable [CharP I p] [CharP J p]

def ofNormEquivWithObserversAndFrobenius
    (obsI : WittVector p I → ℕ → ℝ) (obsJ : WittVector p J → ℕ → ℝ)
    (hI : ∀ (a : WittVector p I) (n : ℕ), obsI a n = ‖a.coeff n‖)
    (hJ : ∀ (a : WittVector p J) (n : ℕ), obsJ a n = ‖a.coeff n‖)
    (e : I ≃+* J) (r : I) (s : J) (h : e r = s)
    (d : ℕ) (hn : ∀ a : I, ‖e a‖ ^ d = ‖a‖) :
    FrobeniusNormData (WittRingEquiv.mapEquiv p e).toEquiv.toFun
      (algebraMap (WittVector p I) (WittPrimeTeichLocalization.Ring p r))
      (algebraMap (WittVector p J) (WittPrimeTeichLocalization.Ring p s))
      (WittPrimeTeichLocalization.denominator p r)
      (WittPrimeTeichLocalization.denominator p s) obsI obsJ d where
  toNormData := ofNormEquivWithObservers p obsI obsJ hI hJ e r s h d hn
  sourceFrobenius := WittPrimeTeichFrobenius.hom p r
  targetFrobenius := WittPrimeTeichFrobenius.hom p s
  on_frobenius := WittPrimeTeichFrobenius.equiv_hom p e r s h

variable
    (obsI : WittVector p I → ℕ → ℝ) (obsJ : WittVector p J → ℕ → ℝ)
    (hI : ∀ (a : WittVector p I) (n : ℕ), obsI a n = ‖a.coeff n‖)
    (hJ : ∀ (a : WittVector p J) (n : ℕ), obsJ a n = ‖a.coeff n‖)
    (e : I ≃+* J) (r : I) (s : J) (h : e r = s)
    (d : ℕ) (hn : ∀ a : I, ‖e a‖ ^ d = ‖a‖)

theorem ofNormEquivWithObserversAndFrobenius_sourceFrobenius :
    (ofNormEquivWithObserversAndFrobenius p obsI obsJ hI hJ e r s h d hn).sourceFrobenius =
      (WittPrimeTeichFrobenius.hom p r :
        WittPrimeTeichLocalization.Ring p r → WittPrimeTeichLocalization.Ring p r) := rfl

theorem ofNormEquivWithObserversAndFrobenius_targetFrobenius :
    (ofNormEquivWithObserversAndFrobenius p obsI obsJ hI hJ e r s h d hn).targetFrobenius =
      (WittPrimeTeichFrobenius.hom p s :
        WittPrimeTeichLocalization.Ring p s → WittPrimeTeichLocalization.Ring p s) := rfl

theorem ofNormEquivWithObserversAndFrobenius_toNormData_eq :
    (ofNormEquivWithObserversAndFrobenius p obsI obsJ hI hJ e r s h d hn).toNormData =
      ofNormEquivWithObservers p obsI obsJ hI hJ e r s h d hn := rfl

end
end JoshiTeich.Act1Scene1.WittMappedFrobeniusData
