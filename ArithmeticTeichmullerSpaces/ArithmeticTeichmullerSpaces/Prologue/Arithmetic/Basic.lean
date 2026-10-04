import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

namespace JoshiTeich.Prologue.Arithmetic

open scoped BigOperators NumberField

variable {K : Type*} [Field K] [NumberField K]

/-!
Finite-place divisors are the arithmetic support used by the height and
different/conductor interfaces.  The support and exponents are data; the
nonzero-exponent condition prevents an empty encoding of a supported divisor.
-/
structure FinitePlaceDivisor (K : Type*) [Field K] [NumberField K] where
  support : Finset (NumberField.FinitePlace K)
  exponent : NumberField.FinitePlace K → ℕ
  exponent_ne_zero : ∀ w ∈ support, exponent w ≠ 0

namespace FinitePlaceDivisor

noncomputable def logDegree (D : FinitePlaceDivisor K) : ℝ :=
  ∑ w ∈ D.support,
    (D.exponent w : ℝ) * Real.log (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ)

lemma logDegree_nonneg (D : FinitePlaceDivisor K) : 0 ≤ D.logDegree := by
  unfold logDegree
  refine Finset.sum_nonneg fun w hw ↦ mul_nonneg (Nat.cast_nonneg _) ?_
  exact Real.log_nonneg (by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w.maximalIdeal).le)

lemma logDegree_pos_of_nonempty (D : FinitePlaceDivisor K) (hD : D.support.Nonempty) :
    0 < D.logDegree := by
  classical
  obtain ⟨w, hw⟩ := hD
  have hw_exp : 0 < D.exponent w := Nat.pos_of_ne_zero (D.exponent_ne_zero w hw)
  have hw_norm : 1 < (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w.maximalIdeal)
  have hw_log : 0 < Real.log (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) :=
    Real.log_pos hw_norm
  refine Finset.sum_pos' (fun w' hw' ↦ ?_) ⟨w, hw, mul_pos (Nat.cast_pos.mpr hw_exp) hw_log⟩
  have hw'_norm : (1 : ℝ) < (Ideal.absNorm w'.maximalIdeal.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w'.maximalIdeal)
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hw'_norm.le)

end FinitePlaceDivisor

/-!
An affine height profile records the finite-place part of the arithmetic height
formula from II.5.  Archimedean terms and arithmeticoid variation remain
separate source obligations instead of being hidden in an arbitrary function.
-/
structure HeightData (K : Type*) [Field K] [NumberField K] where
  places : Finset (NumberField.FinitePlace K)
  weight : NumberField.FinitePlace K → ℝ
  weight_nonneg : ∀ w ∈ places, 0 ≤ weight w
  value : K → ℝ
  value_eq : ∀ x,
    value x = ∑ w ∈ places, weight w * Real.log (max (w x) 1)

theorem HeightData.value_nonneg (H : HeightData K) (x : K) : 0 ≤ H.value x := by
  rw [H.value_eq]
  refine Finset.sum_nonneg fun w hw ↦
    mul_nonneg (H.weight_nonneg w hw) (Real.log_nonneg (le_max_right _ _))

/-! The different is the mathlib ideal; its norm is the absolute discriminant. -/
noncomputable def differentIdeal : Ideal (𝓞 K) :=
  _root_.differentIdeal ℤ (𝓞 K)

theorem differentIdeal_norm_eq_discriminant :
    Ideal.absNorm (differentIdeal (K := K)) = (NumberField.discr K).natAbs := by
  exact NumberField.absNorm_differentIdeal K (𝓞 K)

noncomputable def differentLog : ℝ :=
  Real.log (Ideal.absNorm (differentIdeal (K := K)) : ℝ)

theorem differentLog_nonneg : 0 ≤ differentLog (K := K) := by
  unfold differentLog
  apply Real.log_nonneg
  have hne : Ideal.absNorm (differentIdeal (K := K)) ≠ 0 := by
    change Ideal.absNorm (_root_.differentIdeal ℤ (𝓞 K)) ≠ 0
    intro h
    exact differentIdeal_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne

/-! A source-backed profile for the log-different/log-conductor quantities. -/
structure RamificationProfile (K : Type*) [Field K] [NumberField K] where
  conductor : FinitePlaceDivisor K
  different_log : ℝ
  conductor_log : ℝ
  different_log_nonneg : 0 ≤ different_log
  conductor_log_nonneg : 0 ≤ conductor_log

def RamificationProfile.logTotal (R : RamificationProfile K) : ℝ :=
  R.different_log + R.conductor_log

theorem RamificationProfile.logTotal_nonneg (R : RamificationProfile K) :
    0 ≤ R.logTotal := by
  exact add_nonneg R.different_log_nonneg R.conductor_log_nonneg

end JoshiTeich.Prologue.Arithmetic
