/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Corollary22
import Definitions.Def_AbcAdaptation_Reference_Genl_GeneralPosition_StatementII
import Theorems.Thm_AbcAdaptation_Reference_Iut_Corollary22Inputs_c2
import Theorems.Thm_AbcAdaptation_Reference_Iut_epsilonE_le
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open AbcAdaptation.Reference
open AbcAdaptation.Reference.Iut
open Finset Real
universe u v

namespace AbcAdaptation.Reference.DiscrepancyLE
variable {α : Type*} {f g h : α → ℝ} {s t : Set α}

private theorem trans (h₁ : f ≲[s] g) (h₂ : g ≲[s] h) : f ≲[s] h := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  exact ⟨C₁ + C₂, fun x hx ↦ by have := hC₁ x hx; have := hC₂ x hx; linarith⟩

private theorem mono (hst : t ⊆ s) (hfg : f ≲[s] g) : f ≲[t] g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨C, fun x hx ↦ hC x (hst hx)⟩

@[simp]
private theorem empty : f ≲[(∅ : Set α)] g :=
  ⟨0, by simp⟩

private theorem union (hs : f ≲[s] g) (ht : f ≲[t] g) : f ≲[s ∪ t] g := by
  obtain ⟨C₁, hC₁⟩ := hs
  obtain ⟨C₂, hC₂⟩ := ht
  refine ⟨max C₁ C₂, fun x hx ↦ ?_⟩
  rcases hx with hx | hx
  · exact (hC₁ x hx).trans (by gcongr; exact le_max_left C₁ C₂)
  · exact (hC₂ x hx).trans (by gcongr; exact le_max_right C₁ C₂)

private theorem smul {c : ℝ} (hc : 0 ≤ c) (hfg : f ≲[s] g) : c • f ≲[s] c • g := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨c * C, fun x hx ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  calc c * f x ≤ c * (g x + C) := by
        exact mul_le_mul_of_nonneg_left (hC x hx) hc
    _ = c * g x + c * C := by ring

end AbcAdaptation.Reference.DiscrepancyLE

namespace AbcAdaptation.Reference.DiscrepancyEquiv
variable {α : Type*} {f g : α → ℝ} {s : Set α}

private theorem ge (hfg : f ≈[s] g) : g ≲[s] f := hfg.2

end AbcAdaptation.Reference.DiscrepancyEquiv

namespace AbcAdaptation.Reference.Iut

/-- Any bounded-discrepancy inequality holds on a finite set. -/
private lemma DiscrepancyLE.of_finite {α : Type*} {f g : α → ℝ} {s : Set α} (hs : s.Finite) :
    f ≲[s] g := by
  obtain ⟨C, hC⟩ := (hs.image fun x => f x - g x).bddAbove
  exact ⟨C, fun x hx => by linarith [hC (Set.mem_image_of_mem _ hx)]⟩

end AbcAdaptation.Reference.Iut

theorem AbcAdaptation.Reference.Iut.statementII_of_cor312
    {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {P : Corollary312VariantData.{u, v} AG TG → Prop}
    (I : ∀ (K : T.CBS) (d : ℕ), Corollary22Inputs T K d)
    (ex : ∀ K d, ThetaDataExistence P (I K d))
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ X : Corollary312VariantData.{u, v} AG TG, P X → Corollary312Variant X) :
    T.StatementII := by
  intro d ε hε K
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · rw [hd0, T.ptLE_zero, Set.inter_empty]
    exact DiscrepancyLE.empty
  set S := T.cbsSet K ∩ T.ptLE T.tripod d with hS
  set Id := I K d with hId
  -- the threshold and the finite exceptional set
  have hδ1 : (1 : ℝ) ≤ deltaBound d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold deltaBound; linarith
  set H : ℝ := max (Id.threshold cheb)
    (max (((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4) / ε) ^ 4) 1) with hH
  set Exc : Set (T.Pt T.tripod) :=
    (Id.excCore ∩ S) ∪ {x | x ∈ S ∧ Id.h x ≤ H} with hExc
  have hExc_fin : Exc.Finite := Id.excCore_finite.union (Id.northcott H)
  -- on `S ∖ Exc`, Corollary 2.2 gives the inequality with a uniform number
  have hgood : Id.h ≲[S \ Exc]
      (6 * (1 + ε)) • (T.logDiff T.tripod + T.logCond T.tripod) := by
    refine ⟨6 * (40 * pnt.η + Id.B / 3), fun x hx => ?_⟩
    obtain ⟨hxS, hxE⟩ := hx
    have hxe : x ∉ Id.excCore := fun h => hxE (Or.inl ⟨h, hxS⟩)
    have hxH : H < Id.h x := by
      by_contra hle
      exact hxE (Or.inr ⟨hxS, not_lt.mp hle⟩)
    have hth : Id.threshold cheb ≤ Id.h x := (le_max_left _ _).trans hxH.le
    obtain ⟨hc2, _, hnn⟩ := Id.c2 hd (ex K d) cheb pnt h312 x hxS hxe hth
    have hεE : epsilonE (deltaBound d) (Id.h x) ≤ ε := by
      apply epsilonE_le hδ1 hε
      · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hxH.le
      · exact ((le_max_right _ _).trans (le_max_right _ _)).trans hxH.le
    have : (1 + epsilonE (deltaBound d) (Id.h x)) *
        (T.logDiff T.tripod x + T.logCond T.tripod x) ≤
        (1 + ε) * (T.logDiff T.tripod x + T.logCond T.tripod x) :=
      mul_le_mul_of_nonneg_right (by linarith) hnn
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linarith
  -- `ht ≲ (1/6)·h` on `K`, hence on `S ∖ Exc`
  have hht : T.htCan T.tripod ≲[S \ Exc] (1 / 6 : ℝ) • Id.h :=
    (Id.htCan_equiv.ge).mono fun x hx => hx.1.1
  have hcomb : T.htCan T.tripod ≲[S \ Exc]
      (1 + ε) • (T.logDiff T.tripod + T.logCond T.tripod) := by
    refine hht.trans ?_
    have := hgood.smul (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [smul_smul, show (1 / 6 : ℝ) * (6 * (1 + ε)) = 1 + ε by ring] at this
    exact this
  -- combine with the finite exceptional set
  have hsub : S ⊆ (S \ Exc) ∪ Exc := fun x hx => by
    by_cases h : x ∈ Exc
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  exact (hcomb.union (DiscrepancyLE.of_finite hExc_fin)).mono hsub
