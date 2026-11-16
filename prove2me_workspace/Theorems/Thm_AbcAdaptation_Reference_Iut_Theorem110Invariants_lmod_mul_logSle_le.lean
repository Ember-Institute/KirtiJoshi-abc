/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adapted from Iut/Implication/Theorem110.lean at commit
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8. The complete source proof body is
retained; imports, the namespace and the explicit parameter header are adapted.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Invariants
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open scoped BigOperators
open NumberField
open AbcAdaptation.Reference.Iut
open AbcAdaptation.Reference.Iut.Theorem110Invariants
universe u v

theorem AbcAdaptation.Reference.Iut.Theorem110Invariants.lmod_mul_logSle_le
    {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {X : Corollary312VariantData.{u, v} AG TG}
    (inv : Theorem110Invariants X) (pnt : PrimeCountingBound) :
    inv.lmod * inv.logSle ≤ 3 / 2 * ((inv.eStar : ℝ) * X.ℓ + pnt.η) := by
  set N : ℕ := inv.eStar * X.ℓ with hN
  have hN1 : 2 ≤ N := by
    have h1 := inv.one_le_emod
    have h2 := X.data.prime.five_le
    have h3 : 1 * 5 ≤ inv.emod * X.data.ℓ := Nat.mul_le_mul h1 h2
    simp only [hN, eStar, Corollary312VariantData.ℓ]
    calc 2 ≤ 552960 * (1 * 5) := by norm_num
      _ ≤ 552960 * (inv.emod * X.data.ℓ) := Nat.mul_le_mul_left _ h3
      _ = 552960 * inv.emod * X.data.ℓ := by ring
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNcast : ((inv.eStar : ℝ) * X.ℓ) = N := by simp [hN]
  -- `log(s^≤) ≤ π(N)`
  have hcount : inv.logSle ≤ (Nat.primeCounting N : ℝ) := by
    unfold logSle ι
    rw [Finset.sum_boole]
    have hsub : (inv.dst.filter fun p => p ≤ N) ⊆ Nat.primesLE N := by
      intro p hp
      rw [Finset.mem_filter] at hp
      change p ∈ Nat.primesBelow (N + 1)
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, inv.dst_prime p hp.1⟩
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast Finset.card_le_card hsub
  have hlmod : inv.lmod = Real.log N := by rw [lmod, hNcast]
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hη : 0 < pnt.η := by linarith [pnt.one_lt_η]
  have hlogη : 0 < Real.log pnt.η := Real.log_pos pnt.one_lt_η
  rw [hlmod, hNcast]
  rcases le_or_gt pnt.η N with hle | hlt
  · -- `N ≥ η_prm`: apply the bound at `x = N`
    have hb := pnt.bound N hle
    rw [Nat.floor_natCast] at hb
    calc Real.log N * inv.logSle ≤ Real.log N * (Nat.primeCounting N : ℝ) :=
          mul_le_mul_of_nonneg_left hcount hlogN.le
      _ ≤ Real.log N * (3 * N / (2 * Real.log N)) :=
          mul_le_mul_of_nonneg_left hb hlogN.le
      _ = 3 / 2 * (N : ℝ) := by field_simp
      _ ≤ 3 / 2 * ((N : ℝ) + pnt.η) := by linarith
  · -- `N < η_prm`: `π(N) ≤ π(⌊η_prm⌋)` and apply the bound at `x = η_prm`
    have hb := pnt.bound pnt.η le_rfl
    have hmono : (Nat.primeCounting N : ℝ) ≤ Nat.primeCounting ⌊pnt.η⌋₊ := by
      exact_mod_cast Nat.monotone_primeCounting (Nat.le_floor hlt.le)
    have hlogle : Real.log N ≤ Real.log pnt.η := Real.log_le_log (by linarith) hlt.le
    have hcnt0 : (0 : ℝ) ≤ Nat.primeCounting ⌊pnt.η⌋₊ := by positivity
    calc Real.log N * inv.logSle ≤ Real.log N * (Nat.primeCounting N : ℝ) :=
          mul_le_mul_of_nonneg_left hcount hlogN.le
      _ ≤ Real.log pnt.η * (Nat.primeCounting ⌊pnt.η⌋₊ : ℝ) :=
          mul_le_mul hlogle hmono (by positivity) hlogη.le
      _ ≤ Real.log pnt.η * (3 * pnt.η / (2 * Real.log pnt.η)) :=
          mul_le_mul_of_nonneg_left hb hlogη.le
      _ = 3 / 2 * pnt.η := by field_simp
      _ ≤ 3 / 2 * ((N : ℝ) + pnt.η) := by linarith
