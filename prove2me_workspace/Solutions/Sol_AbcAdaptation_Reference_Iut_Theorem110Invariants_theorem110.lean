/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Parent reduction candidate for the exact theorem110 statement. Complete source
proof body retained. Internal auxiliary proofs are private; accepted public helpers
are imported by their real canonical modules. The only new semantic open child is
LocalEstimate.rhs_le. This draft has not been compiled or submitted. -/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound
import Theorems.Thm_AbcAdaptation_Reference_Iut_assembly
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_pi_le_two
import Theorems.Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic
import Theorems.Thm_AbcAdaptation_Reference_Iut_Theorem110Invariants_sum_arch
import Theorems.Thm_AbcAdaptation_Reference_Iut_Theorem110Invariants_sum_card_standard
import Theorems.Thm_AbcAdaptation_Reference_Iut_Theorem110Invariants_lmod_mul_logSle_le
import Theorems.Thm_AbcAdaptation_Reference_Iut_Theorem110Invariants_iota_nonneg
import Theorems.Thm_AbcAdaptation_Reference_Iut_Theorem110Invariants_LocalEstimate_rhs_le
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open scoped BigOperators
open NumberField
open AbcAdaptation.Reference.Iut
open AbcAdaptation.Reference.Iut.Theorem110Invariants
universe u v

namespace AbcAdaptation.Reference.Iut

private lemma log_pi_nonneg : 0 ≤ Real.log Real.pi :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])

end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Reference.Iut.Corollary312VariantData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (X : Corollary312VariantData.{u, v} AG TG)

private lemma one_le_dmod : 1 ≤ X.dmod :=
  Module.finrank_pos

end AbcAdaptation.Reference.Iut.Corollary312VariantData

namespace AbcAdaptation.Reference.Iut.Corollary312VariantData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (X : Corollary312VariantData.{u, v} AG TG)

private lemma logQAt_nonneg (p : ℕ) : 0 ≤ X.logQAt p := by
  refine Finset.sum_nonneg fun w hw => ?_
  refine mul_nonneg (mul_nonneg (X.qPilot.weight_pos w.1 w.2).le (by positivity)) ?_
  rcases Nat.eq_zero_or_pos (residueChar w.1) with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

end AbcAdaptation.Reference.Iut.Corollary312VariantData

namespace AbcAdaptation.Reference.Iut.Corollary312VariantData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (X : Corollary312VariantData.{u, v} AG TG)

/-- `log(q)` is the sum of its residue-characteristic components over any finite set of
primes containing the residue characteristics of the bad places. -/
private lemma sum_logQAt {s : Finset ℕ} (hbad : ∀ w ∈ X.qPilot.badFinset, residueChar w ∈ s) :
    ∑ p ∈ s, X.logQAt p = X.qPilot.logQ := by
  unfold logQAt QPilotData.logQ
  exact Finset.sum_fiberwise_of_maps_to (fun w _ => hbad w.1 w.2) _

end AbcAdaptation.Reference.Iut.Corollary312VariantData

namespace AbcAdaptation.Reference.Iut.Theorem110Invariants

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

private lemma eStar_cast : (inv.eStar : ℝ) = 552960 * inv.emod := by
  simp only [eStar]; push_cast; ring

end AbcAdaptation.Reference.Iut.Theorem110Invariants

namespace AbcAdaptation.Reference.Iut.Theorem110Invariants

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

private lemma logSle_nonneg : 0 ≤ inv.logSle :=
  Finset.sum_nonneg fun p _ => inv.iota_nonneg p

end AbcAdaptation.Reference.Iut.Theorem110Invariants

namespace AbcAdaptation.Reference.Iut.Theorem110Invariants

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

private lemma logSQ_nonneg : 0 ≤ inv.logSQ :=
  Finset.sum_nonneg fun p hp => Real.log_nonneg (by exact_mod_cast (inv.dst_prime p hp).one_lt.le)

end AbcAdaptation.Reference.Iut.Theorem110Invariants

namespace AbcAdaptation.Reference.Iut.Theorem110Invariants

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

private lemma logDKtot_nonneg : 0 ≤ inv.logDKtot :=
  Finset.sum_nonneg fun p _ => inv.logDK_nonneg p

end AbcAdaptation.Reference.Iut.Theorem110Invariants

namespace AbcAdaptation.Reference.Iut.Theorem110Invariants

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

/-- `ℓ = 2·ℓ* + 1`: the prime `ℓ ≥ 5` is odd. -/
private lemma two_mul_lstar_add_one : 2 * X.lstar + 1 = X.ℓ := by
  have hodd : Odd X.ℓ :=
    X.data.prime.ℓ_prime.odd_of_ne_two (by have := X.data.prime.five_le; omega)
  obtain ⟨k, hk⟩ := hodd
  simp only [Corollary312VariantData.lstar, Corollary312VariantData.ℓ] at hk ⊢
  omega

end AbcAdaptation.Reference.Iut.Theorem110Invariants

namespace AbcAdaptation.Reference.Iut.Theorem110Invariants

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

/-- Step (v), the sum over the capsules of the standard procession of the local bound at
a distinguished prime `p`, via (E1) and (E2). -/
private lemma sum_capsuleBound (L : ℕ) (p : ℕ) :
    ∑ i : Fin L, inv.capsuleBound (i + 2) p =
      (inv.logDK p + 4 * inv.lmod * inv.ι p) * (L * (L + 3) / 2) -
        X.logQAt p / (2 * X.ℓ) * (L * (L + 1) * (2 * L + 1) / 6) + Real.log p * L := by
  calc ∑ i : Fin L, inv.capsuleBound (i + 2) p
      = ∑ i : Fin L, ((inv.logDK p + 4 * inv.lmod * inv.ι p) * ((i : ℝ) + 2) +
          (-(X.logQAt p / (2 * X.ℓ))) * ((i : ℝ) + 1) ^ 2 + Real.log p) :=
        Finset.sum_congr rfl fun i _ => by unfold capsuleBound; push_cast; ring
    _ = _ := by rw [sum_affine_quadratic]; ring

end AbcAdaptation.Reference.Iut.Theorem110Invariants

theorem solution
    {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {X : Corollary312VariantData.{u, v} AG TG}
    (inv : Theorem110Invariants X)
    (cert : Theorem110Certificate inv) (est : inv.LocalEstimate)
    (pnt : PrimeCountingBound) (h312 : Corollary312Variant X) :
    1 / 6 * X.qPilot.logQ ≤
      (1 + 20 * (X.dmod : ℝ) / X.ℓ) * (inv.logDtpd + inv.logFtpd) +
        20 * ((inv.eStar : ℝ) * X.ℓ + pnt.η) := by
  -- notation
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = X.lstar := ⟨_, rfl⟩
  have hℓL : (X.ℓ : ℝ) = 2 * L + 1 := by
    have := two_mul_lstar_add_one (X := X)
    rw [hLdef, ← this]; push_cast; ring
  have hℓ7 : (7 : ℝ) ≤ X.ℓ := by exact_mod_cast cert.seven_le
  have hLpos : (0 : ℝ) < L := by linarith
  have hℓpos : (0 : ℝ) < X.ℓ := by linarith
  -- the summed local bound, evaluated on the standard procession
  have hsum := est.rhs_le
  have hproc : X.rhsData.container.proc = Procession.standard L := by
    rw [hLdef]; exact X.rhsData.proc_standard
  have hlen : (X.rhsData.container.proc.length : ℝ) = L := by
    rw [hproc]
    rfl
  have hs := sum_card_standard hproc
    (fun n => ∑ p ∈ inv.dst, inv.capsuleBound n p + n * Real.log Real.pi)
  beta_reduce at hs
  rw [hlen, hs] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_comm, sum_arch] at hsum
  simp only [sum_capsuleBound] at hsum
  -- the totals over the distinguished primes
  have hQsum : ∑ p ∈ inv.dst, X.logQAt p = X.qPilot.logQ := X.sum_logQAt cert.bad_mem_dst
  have hsum' : ∑ p ∈ inv.dst, ((inv.logDK p + 4 * inv.lmod * inv.ι p) * (L * (L + 3) / 2) -
      X.logQAt p / (2 * X.ℓ) * (L * (L + 1) * (2 * L + 1) / 6) + Real.log p * L) =
      (inv.logDKtot + 4 * inv.lmod * inv.logSle) * (L * (L + 3) / 2) -
        X.qPilot.logQ / (2 * X.ℓ) * (L * (L + 1) * (2 * L + 1) / 6) + inv.logSQ * L := by
    unfold logDKtot logSle logSQ
    rw [← hQsum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  rw [hsum'] at hsum
  -- Corollary 3.12: `−|log(q)| ≤ −|log(Θ)|`
  set q : ℝ := X.qPilot.logQ / (2 * X.ℓ) with hqdef
  have h312' : -q ≤ X.rhsData.rhs := h312
  have hq : X.qPilot.logQ = 2 * X.ℓ * q := by rw [hqdef]; field_simp
  have hrhs := h312'.trans hsum
  rw [le_div_iff₀ hLpos] at hrhs
  -- clear the denominators: multiply by `24ℓ` and cancel `L`
  have hmul := mul_le_mul_of_nonneg_left hrhs (by positivity : (0 : ℝ) ≤ 24 * X.ℓ)
  have hcancel : (L : ℝ) * (-(24 * X.ℓ * q)) ≤
      L * (12 * X.ℓ * (inv.logDKtot + 4 * inv.lmod * inv.logSle) * (L + 3) -
        4 * X.ℓ * q * ((L + 1) * (2 * L + 1)) + 24 * X.ℓ * inv.logSQ +
        12 * X.ℓ * Real.log Real.pi * (L + 3)) := by linarith [hmul]
  have h1L := le_of_mul_le_mul_left hcancel hLpos
  have hLℓ : (L : ℝ) = (X.ℓ - 1) / 2 := by linarith
  rw [hLℓ] at h1L
  have hq1 : X.ℓ * X.qPilot.logQ = 2 * X.ℓ ^ 2 * q := by rw [hq]; ring
  have hq2 : X.ℓ ^ 2 * X.qPilot.logQ = 2 * X.ℓ ^ 3 * q := by rw [hq]; ring
  have h1 : -12 * X.qPilot.logQ ≤ 6 * X.ℓ * (X.ℓ + 5) * inv.logDKtot -
      X.ℓ * (X.ℓ + 1) * X.qPilot.logQ + 24 * X.ℓ * inv.logSQ +
      24 * X.ℓ * (X.ℓ + 5) * (inv.lmod * inv.logSle) +
      6 * X.ℓ * (X.ℓ + 5) * Real.log Real.pi := by
    linarith [h1L, hq, hq1, hq2]
  -- the remaining inputs of the assembly
  have hD := inv.logDKtot_nonneg
  have hQ : 0 ≤ X.qPilot.logQ := hQsum ▸ Finset.sum_nonneg fun p _ => X.logQAt_nonneg p
  have hS := inv.logSQ_nonneg
  have hT : 0 ≤ inv.lmod * inv.logSle :=
    mul_nonneg (Real.log_nonneg (by
      have h1 : (1 : ℝ) ≤ inv.emod := by exact_mod_cast inv.one_le_emod
      have h2 : (5 : ℝ) ≤ X.data.ℓ := by exact_mod_cast X.data.prime.five_le
      have h3 : (1 : ℝ) * 5 ≤ inv.emod * X.data.ℓ :=
        mul_le_mul h1 h2 (by norm_num) (by linarith)
      rw [eStar_cast]; simp only [Corollary312VariantData.ℓ]; linarith)) inv.logSle_nonneg
  have hDF : 0 ≤ inv.logDtpd + inv.logFtpd := by
    linarith [inv.logDtpd_nonneg, inv.logFtpd_nonneg]
  have hlg0 : 0 ≤ Real.log X.ℓ := Real.log_nonneg (by linarith)
  have hlg : Real.log X.ℓ ≤ X.ℓ := by linarith [Real.log_le_sub_one_of_pos hℓpos]
  have hd : (1 : ℝ) ≤ X.dmod := by exact_mod_cast X.one_le_dmod
  have he : 552960 * (X.ℓ : ℝ) ≤ (inv.eStar : ℝ) * X.ℓ := by
    have h1 : (1 : ℝ) ≤ inv.emod := by exact_mod_cast inv.one_le_emod
    have h3 : 1 * (X.ℓ : ℝ) ≤ inv.emod * X.ℓ := mul_le_mul_of_nonneg_right h1 hℓpos.le
    rw [eStar_cast]; linarith
  have hE : (inv.eStar : ℝ) * X.ℓ ≤ (inv.eStar : ℝ) * X.ℓ + pnt.η := by
    linarith [pnt.one_lt_η]
  have h4 := inv.lmod_mul_logSle_le pnt
  have key := assembly hℓ7 hd hD hQ hS hT log_pi_nonneg log_pi_le_two hDF hlg0 hlg he hE h1
    cert.step_ii cert.step_iii (by linarith)
  -- conclude
  have hfinal : (1 + 20 * (X.dmod : ℝ) / X.ℓ) * (inv.logDtpd + inv.logFtpd) +
      20 * ((inv.eStar : ℝ) * X.ℓ + pnt.η) =
      (6 * (X.ℓ + 20 * X.dmod) * (inv.logDtpd + inv.logFtpd) +
        120 * X.ℓ * ((inv.eStar : ℝ) * X.ℓ + pnt.η)) / (6 * X.ℓ) := by
    field_simp; ring
  rw [hfinal, le_div_iff₀ (by positivity)]
  linarith [key]
