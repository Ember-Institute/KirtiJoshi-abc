import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichLocalization
import Mathlib.Analysis.Normed.Group.Defs

/-!
source-id: JT-SCENE1-WITT-MAPPED-LOCALIZATION-COMPARISON-DATA
source: Joshi II `se:ff-rings`, the algebraic localization of W(O_F),
and the coefficient norm-power comparison.
fidelity: stores a localization equivalence and its presentation laws for
an independently specified Witt function. The norm law uses the same
function parameter. The structures use abstract rings, inclusions, and
denominators. The constructor specializes them to the original Witt
localizations and obtains the coefficient law from the coefficient-ring
norm law. Original proofs; no reference implementation copied.
boundary: no completed-ring comparison is asserted. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.WittMappedLocalizationComparisonData

noncomputable section

open WittPrimeTeichLocalization

structure Data {A B L M : Type*}
    [CommRing A] [CommRing B] [CommRing L] [CommRing M]
    (f : A → B) (i : A →+* L) (j : B →+* M) (r : A) (s : B) where
  locEquiv : L ≃+* M
  on_algebraMap :
    ∀ a : A, locEquiv (i a) = j (f a)
  on_presentation :
    ∀ (x : L) (m : ℕ) (a : A),
      x * i r ^ m = i a →
      locEquiv x * j s ^ m = j (f a)

structure NormData {A B L M : Type*}
    [CommRing A] [CommRing B] [CommRing L] [CommRing M]
    (f : A → B) (i : A →+* L) (j : B →+* M) (r : A) (s : B)
    (coefficientNormA : A → ℕ → ℝ) (coefficientNormB : B → ℕ → ℝ)
    (d : ℕ) extends Data f i j r s where
  coeff_norm_pow :
    ∀ (a : A) (n : ℕ), coefficientNormB (f a) n ^ d = coefficientNormA a n

variable (p : ℕ) [Fact p.Prime]
variable {I J : Type*} [CommRing I] [CommRing J] [Norm I] [Norm J]

def ofNormEquivWithObservers
    (obsI : WittVector p I → ℕ → ℝ) (obsJ : WittVector p J → ℕ → ℝ)
    (hI : ∀ (a : WittVector p I) (n : ℕ), obsI a n = ‖a.coeff n‖)
    (hJ : ∀ (a : WittVector p J) (n : ℕ), obsJ a n = ‖a.coeff n‖)
    (e : I ≃+* J) (r : I) (s : J) (h : e r = s)
    (d : ℕ) (hn : ∀ a : I, ‖e a‖ ^ d = ‖a‖) :
    NormData (WittRingEquiv.mapEquiv p e).toEquiv.toFun
      (algebraMap (WittVector p I) (WittPrimeTeichLocalization.Ring p r))
      (algebraMap (WittVector p J) (WittPrimeTeichLocalization.Ring p s))
      (denominator p r) (denominator p s) obsI obsJ d where
  toData := {
    locEquiv := WittPrimeTeichLocalization.equiv p e r s h
    on_algebraMap := WittPrimeTeichLocalization.equiv_algebraMap p e r s h
    on_presentation := WittPrimeTeichLocalization.equiv_presentation p e r s h
  }
  coeff_norm_pow a n := by
    rw [hJ]
    change ‖(WittRingEquiv.mapEquiv p e a).coeff n‖ ^ d = obsI a n
    rw [WittRingEquiv.mapEquiv_coeff, hn]
    exact (hI a n).symm

end
end JoshiTeich.Act1Scene1.WittMappedLocalizationComparisonData
