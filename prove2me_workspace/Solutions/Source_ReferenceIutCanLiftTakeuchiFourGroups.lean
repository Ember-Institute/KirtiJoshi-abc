/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/FourGroups.lean, lines 36–190
-/
import Solutions.Source_ReferenceIutCanLiftFrickeRigidity
import Solutions.Source_ReferenceIutCanLiftTakeuchiMarkov
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
# Takeuchi's four explicit generating pairs

The pairs are in the order of Sijsling's Table 1. Their positive traces identify
the conjugacy class of a pair with one of Takeuchi's four squared trace triples.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open Fricke (tr tr_commutator tr_commutator_eq_neg_two_iff)

/-- Rescale a real matrix of positive determinant `n` to determinant one. -/
noncomputable def scaledSL (n : ℕ) (hn : 0 < n) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M.det = n) : SL(2, ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨(Real.sqrt n)⁻¹ • M, ?_⟩
  rw [det_smul, hM, Fintype.card_fin, inv_pow, Real.sq_sqrt hnR.le, inv_mul_cancel₀ hnR.ne']

private theorem tr_scaledSL (n : ℕ) (hn : 0 < n) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M.det = n) : tr (scaledSL n hn M hM) = M.trace / Real.sqrt n := by
  simp [tr, scaledSL, trace_smul, div_eq_inv_mul]

private theorem tr_scaledSL_mul (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (M N : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det = n) (hN : N.det = k) :
    tr (scaledSL n hn M hM * scaledSL k hk N hN) =
      (M * N).trace / (Real.sqrt n * Real.sqrt k) := by
  change Matrix.trace (((Real.sqrt n)⁻¹ • M) * ((Real.sqrt k)⁻¹ • N)) =
    (M * N).trace / (Real.sqrt n * Real.sqrt k)
  rw [smul_mul_smul_comm, trace_smul, smul_eq_mul, div_eq_inv_mul, mul_inv]

noncomputable def pairIA : SL(2, ℝ) :=
  scaledSL 5 (by norm_num) !![4, 1; -1, 1] (by norm_num [det_fin_two])

noncomputable def pairIB : SL(2, ℝ) :=
  scaledSL 5 (by norm_num) !![3, 2; 8, 7] (by norm_num [det_fin_two])

noncomputable def pairIIA : SL(2, ℝ) :=
  scaledSL 6 (by norm_num) !![5, 1; -1, 1] (by norm_num [det_fin_two])

noncomputable def pairIIB : SL(2, ℝ) :=
  scaledSL 3 (by norm_num) !![2, 1; 5, 4] (by norm_num [det_fin_two])

noncomputable def pairIIIA : SL(2, ℝ) :=
  scaledSL 2 (by norm_num) !![3, 1; 1, 1] (by norm_num [det_fin_two])

noncomputable def pairIIIB : SL(2, ℝ) :=
  scaledSL 2 (by norm_num) !![1, 1; 1, 3] (by norm_num [det_fin_two])

noncomputable def pairIVA : SL(2, ℝ) :=
  scaledSL 1 (by norm_num) !![2, 1; 1, 1] (by norm_num [det_fin_two])

noncomputable def pairIVB : SL(2, ℝ) :=
  scaledSL 1 (by norm_num) !![0, -1; 1, 3] (by norm_num [det_fin_two])

/-- The four explicit pairs in order I, II, III, IV. -/
noncomputable def takeuchiPair : Fin 4 → SL(2, ℝ) × SL(2, ℝ)
  | 0 => (pairIA, pairIB)
  | 1 => (pairIIA, pairIIB)
  | 2 => (pairIIIA, pairIIIB)
  | 3 => (pairIVA, pairIVB)

private theorem div_sqrt_eq_sqrt {t n X : ℝ} (ht : 0 ≤ t) (hn : 0 < n)
    (h : t ^ 2 = X * n) : t / Real.sqrt n = Real.sqrt X := by
  have hX : 0 ≤ X := nonneg_of_mul_nonneg_left (h ▸ sq_nonneg t) hn
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hX (by positivity), div_mul_div_comm,
    Real.mul_self_sqrt hn.le, eq_div_iff_mul_eq hn.ne']
  simpa only [pow_two] using h.symm

private theorem div_sqrt_mul_sqrt_eq_sqrt {t n k X : ℝ} (ht : 0 ≤ t) (hn : 0 < n) (hk : 0 < k)
    (h : t ^ 2 = X * (n * k)) : t / (Real.sqrt n * Real.sqrt k) = Real.sqrt X := by
  rw [← Real.sqrt_mul hn.le]
  exact div_sqrt_eq_sqrt ht (mul_pos hn hk) h

/-- The positive trace triples of the four pairs in order I, II, III, IV. -/
theorem takeuchiPair_traces :
    (tr pairIA = Real.sqrt 5 ∧ tr pairIB = Real.sqrt 20 ∧ tr (pairIA * pairIB) = Real.sqrt 25) ∧
    (tr pairIIA = Real.sqrt 6 ∧ tr pairIIB = Real.sqrt 12 ∧
      tr (pairIIA * pairIIB) = Real.sqrt 18) ∧
    (tr pairIIIA = Real.sqrt 8 ∧ tr pairIIIB = Real.sqrt 8 ∧
      tr (pairIIIA * pairIIIB) = Real.sqrt 16) ∧
    (tr pairIVA = Real.sqrt 9 ∧ tr pairIVB = Real.sqrt 9 ∧
      tr (pairIVA * pairIVB) = Real.sqrt 9) := by
  simp only [pairIA, pairIB, pairIIA, pairIIB, pairIIIA, pairIIIB, pairIVA, pairIVB,
    tr_scaledSL, tr_scaledSL_mul]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    first
    | (apply div_sqrt_eq_sqrt <;> norm_num [trace_fin_two])
    | (apply div_sqrt_mul_sqrt_eq_sqrt <;> norm_num [trace_fin_two, mul_apply, Fin.sum_univ_two])

private theorem tr_neg (A : SL(2, ℝ)) : tr (-A) = -tr A := by
  simp only [tr, Matrix.SpecialLinearGroup.coe_neg, trace_neg]

/-- If the product of the traces is positive, choose generator signs so that each trace is
its absolute value. These signs preserve the commutator trace. -/
theorem exists_sign_normalize {A B : SL(2, ℝ)} (hpos : 0 < tr A * tr B * tr (A * B)) :
    ∃ A' ∈ ({A, -A} : Set SL(2, ℝ)), ∃ B' ∈ ({B, -B} : Set SL(2, ℝ)),
      tr A' = |tr A| ∧ tr B' = |tr B| ∧ tr (A' * B') = |tr (A * B)| ∧
      tr (A' * B' * A'⁻¹ * B'⁻¹) = tr (A * B * A⁻¹ * B⁻¹) := by
  have hx : tr A ≠ 0 := by
    intro h
    simp [h] at hpos
  have hy : tr B ≠ 0 := by
    intro h
    simp [h] at hpos
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · have hz : 0 < tr (A * B) :=
      pos_of_mul_pos_right hpos (mul_pos_of_neg_of_neg hx hy).le
    refine ⟨-A, by simp, -B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [tr_neg, abs_of_neg hx]
    · rw [tr_neg, abs_of_neg hy]
    · rw [neg_mul_neg, abs_of_pos hz]
    · rw [tr_commutator (-A) (-B), tr_commutator A B]
      simp only [tr_neg, neg_mul_neg]
      ring
  · have hz : tr (A * B) < 0 :=
      neg_of_mul_pos_right hpos (mul_neg_of_neg_of_pos hx hy).le
    refine ⟨-A, by simp, B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [tr_neg, abs_of_neg hx]
    · rw [abs_of_pos hy]
    · rw [neg_mul, tr_neg, abs_of_neg hz]
    · rw [tr_commutator (-A) (B), tr_commutator A B]
      simp only [tr_neg, neg_mul]
      ring
  · have hz : tr (A * B) < 0 :=
      neg_of_mul_pos_right hpos (mul_neg_of_pos_of_neg hx hy).le
    refine ⟨A, by simp, -B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_pos hx]
    · rw [tr_neg, abs_of_neg hy]
    · rw [mul_neg, tr_neg, abs_of_neg hz]
    · rw [tr_commutator (A) (-B), tr_commutator A B]
      simp only [tr_neg, mul_neg]
      ring
  · have hz : 0 < tr (A * B) := pos_of_mul_pos_right hpos (mul_pos hx hy).le
    exact ⟨A, by simp, B, by simp, (abs_of_pos hx).symm, (abs_of_pos hy).symm,
      (abs_of_pos hz).symm, rfl⟩

/-- A pair with commutator trace `-2` and one of Takeuchi's squared trace triples is
simultaneously conjugate to an explicit pair in `GL(2, ℝ)` after changing generator signs. -/
theorem exists_conj_of_takeuchiSq {A' B' : SL(2, ℝ)} (hc' : tr (A' * B' * A'⁻¹ * B'⁻¹) = -2)
    (hT : TakeuchiSq (tr A') (tr B') (tr (A' * B'))) :
    ∃ i : Fin 4, ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
      ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1 ∧
        g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2 := by
  have hrel := (tr_commutator_eq_neg_two_iff A' B').mp hc'
  have hX : 4 < tr A' ^ 2 := by
    rcases hT with h | h | h | h <;> rw [h.1] <;> norm_num
  have hpos : 0 < tr A' * tr B' * tr (A' * B') := by
    rw [← hrel]
    have hApos := lt_trans (by norm_num : (0 : ℝ) < 4) hX
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hApos (sq_nonneg _)) (sq_nonneg _)
  obtain ⟨A'', hA'', B'', hB'', h1, h2, h3, h4⟩ := exists_sign_normalize hpos
  have hx'' : 4 < tr A'' ^ 2 := by rw [h1, sq_abs]; exact hX
  have hc'' : tr (A'' * B'' * A''⁻¹ * B''⁻¹) ≠ 2 := by rw [h4, hc']; norm_num
  obtain ⟨⟨t1a, t1b, t1c⟩, ⟨t2a, t2b, t2c⟩, ⟨t3a, t3b, t3c⟩, ⟨t4a, t4b, t4c⟩⟩ :=
    takeuchiPair_traces
  simp only [← Real.sqrt_sq_eq_abs] at h1 h2 h3
  rcases hT with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · obtain ⟨g, hg1, hg2⟩ := SL2R.exists_conj_of_tr_eq (A' := pairIVA) (B' := pairIVB) hx'' hc''
      (by rw [h1, ha, t4a]) (by rw [h2, hb, t4b]) (by rw [h3, hc, t4c])
    exact ⟨3, A'', hA'', B'', hB'', g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := SL2R.exists_conj_of_tr_eq (A' := pairIIIA) (B' := pairIIIB) hx'' hc''
      (by rw [h1, ha, t3a]) (by rw [h2, hb, t3b]) (by rw [h3, hc, t3c])
    exact ⟨2, A'', hA'', B'', hB'', g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := SL2R.exists_conj_of_tr_eq (A' := pairIA) (B' := pairIB) hx'' hc''
      (by rw [h1, ha, t1a]) (by rw [h2, hb, t1b]) (by rw [h3, hc, t1c])
    exact ⟨0, A'', hA'', B'', hB'', g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := SL2R.exists_conj_of_tr_eq (A' := pairIIA) (B' := pairIIB) hx'' hc''
      (by rw [h1, ha, t2a]) (by rw [h2, hb, t2b]) (by rw [h3, hc, t2c])
    exact ⟨1, A'', hA'', B'', hB'', g, hg1, hg2⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
