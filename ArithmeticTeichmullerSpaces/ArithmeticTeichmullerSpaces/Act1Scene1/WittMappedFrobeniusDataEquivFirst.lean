import ArithmeticTeichmullerSpaces.Act1Scene1.WittMappedFrobeniusData

/-!
source-id: JT-SCENE1-WITT-MAPPED-FROBENIUS-DATA-EQUIV-FIRST
source: Joshi II `se:ff-rings`, functorial Frobenius and coefficient norm
comparison for integral Witt localizations.
fidelity: fixes the original coefficient equivalence and all its operation
instances before accepting norm observers. Returns the same proved generic
Frobenius data, without changing any map, carrier or law. Original proof;
no reference implementation copied. Prologue R5 unchanged.
boundary: generic construction only; concrete specialization and all
original-map, completion and paper identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.WittMappedFrobeniusData

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {I J : Type*} [CommRing I] [CommRing J]

def ofEquiv
    (e : I ≃+* J) [Norm I] [Norm J] [CharP I p] [CharP J p]
    (obsI : WittVector p I → ℕ → ℝ) (obsJ : WittVector p J → ℕ → ℝ)
    (hI : ∀ (a : WittVector p I) (n : ℕ), obsI a n = ‖a.coeff n‖)
    (hJ : ∀ (a : WittVector p J) (n : ℕ), obsJ a n = ‖a.coeff n‖)
    (r : I) (s : J) (h : e r = s)
    (d : ℕ) (hn : ∀ a : I, ‖e a‖ ^ d = ‖a‖) :=
  ofNormEquivWithObserversAndFrobenius p obsI obsJ hI hJ e r s h d hn

end
end JoshiTeich.Act1Scene1.WittMappedFrobeniusData
