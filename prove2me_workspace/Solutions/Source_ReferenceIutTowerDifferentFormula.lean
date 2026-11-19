/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/Different.lean
-/
import Solutions.Source_ReferenceIutTowerLocalFacts
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain
open scoped BigOperators

universe u

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-- The normalized logarithmic different degree in the tower `F_tpd ⊆ K`. -/
theorem logDifferentDeg_torsionField_eq :
    logDifferentDeg ↥Pr.torsionField = logDifferentDeg ↥(tripodalFieldOf F E) +
      Real.log (Ideal.absNorm
        (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField))) /
        Module.finrank ℚ ↥Pr.torsionField := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := ↥(tripodalFieldOf F E)) (𝒪 := 𝓞 ↥(tripodalFieldOf F E)) (L := ↥Pr.torsionField)
    (𝒪' := 𝓞 ↥Pr.torsionField)
  rw [← absNorm_differentIdeal ↥Pr.torsionField (𝓞 ↥Pr.torsionField),
    ← absNorm_differentIdeal ↥(tripodalFieldOf F E) (𝓞 ↥(tripodalFieldOf F E))] at h
  have hD : Ideal.absNorm (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr differentIdeal_ne_bot
  have hT : Ideal.absNorm (differentIdeal ℤ (𝓞 ↥(tripodalFieldOf F E))) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr differentIdeal_ne_bot
  have hKT : (Module.finrank ↥(tripodalFieldOf F E) ↥Pr.torsionField : ℝ) ≠ 0 := by
    letI : FiniteDimensional ↥(tripodalFieldOf F E) ↥Pr.torsionField :=
      Module.Finite.of_restrictScalars_finite ℚ _ _
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ↥(tripodalFieldOf F E) ↥Pr.torsionField).ne'
  unfold logDifferentDeg
  rw [h, Nat.cast_mul, Nat.cast_pow, Real.log_mul (by exact_mod_cast hD)
      (pow_ne_zero _ (by exact_mod_cast hT)),
    Real.log_pow, ← Module.finrank_mul_finrank ℚ ↥(tripodalFieldOf F E) ↥Pr.torsionField,
    Nat.cast_mul, add_div, add_comm]
  congr 1
  rw [mul_comm ((Module.finrank ↥(tripodalFieldOf F E) ↥Pr.torsionField : ℕ) : ℝ),
    mul_div_mul_right _ _ hKT]

/-- The contribution of the four residue characteristics for `5 ≤ ℓ`. -/
lemma sum_one_add_wildConst_le (ℓ : ℕ) (hℓ : 5 ≤ ℓ) :
    ∑ p ∈ ({2, 3, 5, ℓ} : Finset ℕ), (1 + wildConst ℓ p) * Real.log p ≤
      13 * Real.log 2 + 3 * Real.log 3 + 2 * Real.log 5 + 2 * Real.log ℓ := by
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  rcases eq_or_ne ℓ 5 with rfl | h5
  · have h : ({2, 3, 5, 5} : Finset ℕ) = {2, 3, 5} := by decide
    rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [wildConst]
    norm_num <;> linarith
  · have h2 : ℓ ≠ 2 := by omega
    have h3 : ℓ ≠ 3 := by omega
    rw [Finset.sum_insert (by simp [h2.symm]), Finset.sum_insert (by simp [h3.symm]),
      Finset.sum_insert (by simp [h5.symm]), Finset.sum_singleton]
    simp only [wildConst, h2, h3, h5, h2.symm, h3.symm, h5.symm]
    norm_num <;> linarith

/-- `13·log 2 + 3·log 3 + 2·log 5 ≤ 21`. -/
lemma constant_le_21 : 13 * Real.log 2 + 3 * Real.log 3 + 2 * Real.log 5 ≤ 21 := by
  have h2 := Real.log_two_lt_d9
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    calc
      Real.log 3 ≤ Real.log ((2 : ℝ) ^ (2 : ℕ)) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := Real.log_pow 2 2
  have h5 : Real.log 5 ≤ 3 * Real.log 2 := by
    calc
      Real.log 5 ≤ Real.log ((2 : ℝ) ^ (3 : ℕ)) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 3 * Real.log 2 := Real.log_pow 2 3
  linarith

end AbcAdaptation.Reference.Iut
