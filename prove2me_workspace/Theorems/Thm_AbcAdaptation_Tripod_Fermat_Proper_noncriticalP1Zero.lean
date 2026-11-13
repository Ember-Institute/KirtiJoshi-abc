/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/NoncriticalP1/Main.lean core_key and exists_isNoncriticalBelyi (τ = some 0).
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: 368d9baac49838deaf503d72a334b197996b79fe17282f54a44c365c8ab850c4.
-/
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1Normalize
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1Rational
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1Minpoly

set_option autoImplicit false

open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

open NoncriticalP1

private lemma core_key (d : ℕ) : ∀ (n : ℕ) (T : Finset Tripod.Qbar), IsGalStable T →
    (∀ t ∈ T, deg t ≤ d) → (T.filter fun t => deg t = d).card ≤ n →
    ∀ τ : ℚ, (τ : Tripod.Qbar) ∉ T → ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat τ) := by
  classical
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  by_cases hd : d ≤ 1
  · -- all points are rational: normalise and apply Lemma 2.2
    intro n T hT hdeg _ τ hτ
    obtain ⟨u, T₁, hT₁, hbd, hdeg₁, hgood⟩ := noncriticalP1Normalize T hT hτ
    have h1 : ∀ y ∈ T₁, deg y ≤ 1 := (hdeg₁ 1 le_rfl (fun t ht => (hdeg t ht).trans hd)).1
    obtain ⟨hs, hhs⟩ := noncriticalP1Rational T₁ hbd h1
    exact ⟨u :: hs, hgood hs hhs⟩
  · have hd : 2 ≤ d := by omega
    -- if no point has degree `d`, the outer induction hypothesis applies
    have hlower : ∀ T : Finset Tripod.Qbar, IsGalStable T → (∀ t ∈ T, deg t ≤ d) →
        (T.filter fun t => deg t = d).card = 0 →
        ∀ τ : ℚ, (τ : Tripod.Qbar) ∉ T → ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat τ) := by
      intro T hT hdeg h0 τ hτ
      have hb' : ∀ t ∈ T, deg t ≤ d - 1 := by
        intro t ht
        have hne : deg t ≠ d := fun h => by
          have hmem : t ∈ T.filter fun t => deg t = d := Finset.mem_filter.mpr ⟨ht, h⟩
          rw [Finset.card_eq_zero.mp h0] at hmem
          exact Finset.notMem_empty t hmem
        have := hdeg t ht
        omega
      exact ihd (d - 1) (by omega) _ T hT hb' le_rfl τ hτ
    intro n
    induction n with
    | zero =>
      intro T hT hdeg hcard τ hτ
      exact hlower T hT hdeg (Nat.le_zero.mp hcard) τ hτ
    | succ n ihn =>
      intro T hT hdeg hcard τ hτ
      obtain ⟨u, T₁, hT₁, hbd, hdeg₁, hgood⟩ := noncriticalP1Normalize T hT hτ
      obtain ⟨hdeg₁', hcard₁⟩ := hdeg₁ d (by omega) hdeg
      have hcard₁' := (hcard₁ hd).trans hcard
      have h9 : ((9 : ℚ) : Tripod.Qbar) ∉ T₁ := fun h => by
        have := hbd _ h
        rw [norm_ι_ratCast] at this
        norm_num at this
      by_cases h0 : (T₁.filter fun y => deg y = d).card = 0
      · obtain ⟨hs, hhs⟩ := hlower T₁ hT₁ hdeg₁' h0 9 h9
        exact ⟨u :: hs, hgood hs hhs⟩
      · obtain ⟨σ₀, hσ₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
        obtain ⟨hσ₀T, hσ₀d⟩ := Finset.mem_filter.mp hσ₀
        obtain ⟨T₂, τ₂, hT₂, hτ₂, hdeg₂, hcard₂, v, hv⟩ :=
          noncriticalP1Minpoly T₁ hT₁ hbd hd hdeg₁' hcard₁' hσ₀T hσ₀d
        obtain ⟨hs, hhs⟩ := ihn T₂ hT₂ hdeg₂ hcard₂ τ₂ hτ₂
        exact ⟨u :: v :: hs, hgood _ (hv hs hhs)⟩

/-- **Lemma 2.4 combined with Lemma 2.2**: for a finite Galois-stable `T ⊆ ℚ̄` and a rational
`τ ∉ T` there is a noncritical Belyi map for `(T ∪ {∞}, τ)`. -/
private theorem exists_isNoncriticalBelyi_withInf (T : Finset Tripod.Qbar) (hT : IsGalStable T) {τ : ℚ}
    (hτ : (τ : Tripod.Qbar) ∉ T) : ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat τ) :=
  core_key _ _ T hT (fun _ ht => Finset.le_sup (f := deg) ht) le_rfl τ hτ

/-- The actual P¹ noncritical theorem at zero. The combination proof is
ported from the pinned source; mathematical debt is isolated in the three
source reduction steps imported above. -/
theorem noncriticalP1Zero (S : Finset NoncriticalP1.Pt)
    (hGal : ∀ σ : Tripod.Qbar ≃ₐ[ℚ] Tripod.Qbar, ∀ z ∈ S, z.map σ ∈ S)
    (hZero : some 0 ∉ S) :
    ∃ hs : List NoncriticalP1.ElemMap,
      (∀ z ∈ S, NoncriticalP1.evalComp hs z ∈ NoncriticalP1.zeroOneInf) ∧
      NoncriticalP1.evalComp hs (some 0) ∉ NoncriticalP1.zeroOneInf ∧
      (∀ z, 1 < NoncriticalP1.ramIdxComp hs z →
        NoncriticalP1.evalComp hs z ∈ NoncriticalP1.zeroOneInf) := by
  classical
  set T : Finset Tripod.Qbar := S.eraseNone with hTdef
  have hT : IsGalStable T := by
    intro σ t ht
    rw [hTdef, Finset.mem_eraseNone] at ht ⊢
    exact hGal σ _ ht
  have hST : (S : Set NoncriticalP1.Pt) ⊆ withInf T := by
    intro z hz
    cases z with
    | none => exact none_mem_withInf T
    | some t => exact some_mem_withInf (Finset.mem_eraseNone.mpr hz)
  have hq : ((0 : ℚ) : Tripod.Qbar) ∉ T := by
    rw [Finset.mem_eraseNone]
    simpa using hZero
  obtain ⟨hs, hhs⟩ := exists_isNoncriticalBelyi_withInf T hT hq
  have hfinal := IsNoncriticalBelyi.mono hhs hST
  exact ⟨hs, hfinal.1, by simpa [ofRat] using hfinal.2.1, hfinal.2.2⟩

end AbcAdaptation.Tripod.Fermat.Proper
