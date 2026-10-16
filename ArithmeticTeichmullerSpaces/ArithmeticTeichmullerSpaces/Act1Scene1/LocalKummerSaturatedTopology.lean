import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedPadicModule
import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Hausdorff

/-!
source-id: JT-SCENE1-SATURATED-KUMMER-TOPOLOGY
source: original standard H1 quotient, its closed finite-dimensional
boundary space, and the established ordinary-log linear equivalence.
fidelity: on a finite-dimensional local field, the existing saturated
Kummer subspace with its inherited topology is continuously linearly
equivalent to the field by the original ordinary logarithm.
boundary: Scene1/Derived; no H1e/BK identification is asserted.
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)

/-- The actual rational coefficient is the usual Hausdorff one-dimensional Q_p space. -/
theorem rationalH1_t2 : T2Space H := by
  have : T2Space (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p) :=
    inferInstanceAs (T2Space (ULift.{v} ℚ_[p]))
  have : FiniteDimensional ℚ_[p] (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p) :=
    (ContinuousLinearEquiv.ulift : ULift.{v} ℚ_[p] ≃L[ℚ_[p]] ℚ_[p]).toLinearEquiv.symm.finiteDimensional
  exact ContinuousH1Hausdorff.t2_h1 _

variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k] [FiniteDimensional ℚ_[p] k]

/-- Both topologies are the pre-existing ones; neither is transported through log. -/
def saturatedPadicLogContinuousEquiv :
    saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk ≃L[ℚ_[p]] k := by
  have := rationalH1_t2 (k := k) (Ω := Ω) p
  have : FiniteDimensional ℚ_[p] (saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk) :=
    (saturatedPadicLogEquiv (Ω := Ω) p hpk).symm.finiteDimensional
  exact (saturatedPadicLogEquiv p hpk).toContinuousLinearEquiv

theorem saturatedPadicLogContinuousEquiv_apply
    (x : saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk) :
    saturatedPadicLogContinuousEquiv p hpk x = saturatedImageLog p hpk ⟨x.1, x.2⟩ := rfl

theorem saturatedPadicLog_continuous : Continuous (saturatedPadicLog (Ω := Ω) p hpk) :=
  (saturatedPadicLogContinuousEquiv (Ω := Ω) p hpk).continuous

/-- The inverse retains the original standard H1 class and is continuous into ambient H1. -/
def saturatedExpToPadicH1 : k →L[ℚ_[p]] H :=
  (saturatedKummerPadicSubmodule p hpk).subtypeL.comp
    (saturatedPadicLogContinuousEquiv (Ω := Ω) p hpk).symm.toContinuousLinearMap

theorem saturatedExpToPadicH1_apply (y : k) :
    saturatedExpToPadicH1 (Ω := Ω) p hpk y = (saturatedExp (Ω := Ω) p hpk y : H) := by
  have he := (saturatedPadicLogEquiv (Ω := Ω) p hpk).apply_symm_apply y
  apply congrArg Subtype.val
  apply saturatedImageLog_injective p hpk
  exact he.trans ((saturatedLogEquiv (Ω := Ω) p hpk).apply_symm_apply y).symm

end
end JoshiTeich.Act1Scene1.LocalPadicLog
