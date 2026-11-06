import ArithmeticTeichmullerSpaces.Act1Scene1.WittMappedLocalizationComparisonData
import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichFrobenius

/-!
source-id: JT-SCENE1-WITT-MAPPED-FROBENIUS-COMPARISON-DATA
source: Joshi II `se:ff-rings`, Frobenius naturality for integral Witt
localizations and the coefficient norm-power comparison.
fidelity: proves Frobenius commutation for the exact localization
equivalence stored by ofNormEquivWithObservers. The proof uses the
original coefficient-induced localization equivalence and generic forward
Frobenius maps. All observer and norm inputs retain the constructor's
parameter order. No additional comparison certificate is required.
Original proof; no reference implementation copied.
boundary: algebraic forward Frobenius only; concrete original-map
identities, completion and paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.WittMappedFrobeniusComparisonData

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable {I J : Type*} [CommRing I] [CommRing J] [Norm I] [Norm J]
variable [CharP I p] [CharP J p]

theorem ofNormEquivWithObservers_frobenius
    (obsI : WittVector p I → ℕ → ℝ) (obsJ : WittVector p J → ℕ → ℝ)
    (hI : ∀ (a : WittVector p I) (n : ℕ), obsI a n = ‖a.coeff n‖)
    (hJ : ∀ (a : WittVector p J) (n : ℕ), obsJ a n = ‖a.coeff n‖)
    (e : I ≃+* J) (r : I) (s : J) (h : e r = s)
    (d : ℕ) (hn : ∀ a : I, ‖e a‖ ^ d = ‖a‖)
    (x : WittPrimeTeichLocalization.Ring p r) :
    (WittMappedLocalizationComparisonData.ofNormEquivWithObservers
      p obsI obsJ hI hJ e r s h d hn).locEquiv
        (WittPrimeTeichFrobenius.hom p r x) =
      WittPrimeTeichFrobenius.hom p s
        ((WittMappedLocalizationComparisonData.ofNormEquivWithObservers
          p obsI obsJ hI hJ e r s h d hn).locEquiv x) := by
  exact WittPrimeTeichFrobenius.equiv_hom p e r s h x

end
end JoshiTeich.Act1Scene1.WittMappedFrobeniusComparisonData
