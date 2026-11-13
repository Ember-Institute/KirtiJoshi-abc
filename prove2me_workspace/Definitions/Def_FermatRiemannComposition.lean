/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Source proof adaptation: Belyi/CurveField/Riemann.lean:287-395 at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatRiemannSpaces
import Mathlib.Algebra.Module.Submodule.Union

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- Three concrete dimension facts give exact polar realization for every
effective divisor of sufficiently large degree. This is the source's
finite union argument in the actual Riemann–Roch spaces. -/
theorem largeEffectivePolarRealization_of_riemannChildren
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hFinite : ∀ A : Divisor M, FiniteDimensional ℚ (riemannRochSpace M hDVR A))
    (hUpper : ∀ A : Divisor M, (riemannEll M hDVR A : ℤ) ≤
      max 0 (divisorDegree M A + (riemannEll M hDVR 0 : ℤ)))
    (hRiemann : ∃ g0 N0 : ℤ, ∀ A : Divisor M, N0 ≤ divisorDegree M A →
      (riemannEll M hDVR A : ℤ) = divisorDegree M A - g0) :
    ∃ N1 : ℤ, ∀ A : Divisor M, 0 ≤ A → N1 ≤ divisorDegree M A →
      ∃ f : M.K, ∀ P : Place M.K, poleMultiplicity M hDVR f P = A P := by
  classical
  letI : IsCurveField M.K := M.isCurveField
  obtain ⟨g0, N0, hN0⟩ := hRiemann
  set T : ℤ := max 0 (N0 + riemannEll M hDVR 0)
  refine ⟨max (max N0 1) (T + g0 + 1), fun A hA hdeg => ?_⟩
  letI : FiniteDimensional ℚ (riemannRochSpace M hDVR A) := hFinite A
  have hdN0 : N0 ≤ divisorDegree M A :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hdeg
  have hd1 : 1 ≤ divisorDegree M A :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hdeg
  have hdT : T + g0 + 1 ≤ divisorDegree M A := le_trans (le_max_right _ _) hdeg
  have hellA := hN0 A hdN0
  have hlt : ∀ P : Place M.K,
      riemannEll M hDVR (A - Finsupp.single P 1) < riemannEll M hDVR A := by
    intro P
    have hP := P.degree_pos
    by_cases hP' : N0 ≤ divisorDegree M (A - Finsupp.single P 1)
    · have := hN0 _ hP'
      rw [divisorDegree_sub, divisorDegree_single, one_mul] at this
      have : (riemannEll M hDVR (A - Finsupp.single P 1) : ℤ) <
          riemannEll M hDVR A := by
        rw [this, hellA]
        omega
      exact_mod_cast this
    · have h1 := hUpper (A - Finsupp.single P 1)
      have h2 : max 0 (divisorDegree M (A - Finsupp.single P 1) +
          (riemannEll M hDVR 0 : ℤ)) ≤ T :=
        max_le_max le_rfl (by omega)
      have : (riemannEll M hDVR (A - Finsupp.single P 1) : ℤ) <
          riemannEll M hDVR A := by
        rw [hellA]
        omega
      exact_mod_cast this
  let p : A.support → Submodule ℚ (riemannRochSpace M hDVR A) := fun P =>
    (riemannRochSpace M hDVR (A - Finsupp.single P.1 1)).comap
      (riemannRochSpace M hDVR A).subtype
  have hp : ∀ P, p P ≠ ⊤ := by
    intro P h
    letI : FiniteDimensional ℚ
      (riemannRochSpace M hDVR (A - Finsupp.single P.1 1)) := hFinite _
    have hle : riemannRochSpace M hDVR A ≤
        riemannRochSpace M hDVR (A - Finsupp.single P.1 1) := fun f hf => by
      have : (⟨f, hf⟩ : riemannRochSpace M hDVR A) ∈ p P := h ▸ Submodule.mem_top
      exact this
    exact absurd (Submodule.finrank_mono hle) (not_le.mpr (hlt P.1))
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  have hA0 : A ≠ 0 := by
    rintro rfl
    simp at hd1
  obtain ⟨P0, hP0⟩ := Finsupp.support_nonempty_iff.mpr hA0
  have hv0 : (v : M.K) ≠ 0 := by
    intro h
    apply hv ⟨P0, hP0⟩
    change (v : M.K) ∈ riemannRochSpace M hDVR _
    rw [h]
    exact Submodule.zero_mem _
  have hvL := ((mem_riemannRochSpace M hDVR A v).mp v.2).resolve_left hv0
  refine ⟨v, fun Q => ?_⟩
  rw [poleMultiplicity]
  by_cases hQ : Q ∈ A.support
  · have hnot : (v : M.K) ∉ riemannRochSpace M hDVR (A - Finsupp.single Q 1) :=
      hv ⟨Q, hQ⟩
    rw [mem_riemannRochSpace, not_or] at hnot
    obtain ⟨R, hR⟩ := not_forall.mp hnot.2
    have hRQ : R = Q := by
      by_contra hne
      apply hR
      simpa [Finsupp.single_apply, Ne.symm hne] using hvL R
    subst hRQ
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same, not_le] at hR
    have := hvL R
    have := hA R
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  · rw [Finsupp.notMem_support_iff.mp hQ]
    have := hvL Q
    rw [Finsupp.notMem_support_iff.mp hQ] at this
    omega

/-- The source's positive-part argument produces the exact existing
PolarPresentation. The auxiliary divisor is constructed from an actual place,
with a degree calculated from its actual residue field. -/
theorem polarPresentation_of_largeEffectivePolarRealization
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hRealize : ∃ N1 : ℤ, ∀ A : Divisor M, 0 ≤ A → N1 ≤ divisorDegree M A →
      ∃ f : M.K, ∀ P : Place M.K, poleMultiplicity M hDVR f P = A P)
    (D : Divisor M) : Nonempty (PolarPresentation M hDVR D) := by
  classical
  letI : IsCurveField M.K := M.isCurveField
  obtain ⟨N1, hN1⟩ := hRealize
  obtain P0 : Place M.K := Classical.arbitrary _
  let E : Divisor M := Finsupp.single P0 (N1.toNat : ℤ)
  have hE : 0 ≤ E := Finsupp.single_nonneg.mpr (Int.natCast_nonneg _)
  have hdegE : N1 ≤ divisorDegree M E := by
    rw [divisorDegree_single]
    have := P0.degree_pos
    have h1 : N1 ≤ (N1.toNat : ℤ) := Int.self_le_toNat N1
    have h2 : (0 : ℤ) ≤ N1.toNat := Int.natCast_nonneg _
    nlinarith
  have key : ∀ A : Divisor M, 0 ≤ A → ∃ f : M.K,
      ∀ P : Place M.K, poleMultiplicity M hDVR f P = (A + E) P := by
    intro A hA
    exact hN1 _ (add_nonneg hA hE) (by
      rw [divisorDegree_add]
      have := divisorDegree_nonneg M hA
      omega)
  obtain ⟨f, hf⟩ := key _ (divisorPosPart_nonneg D)
  obtain ⟨g, hg⟩ := key _ (divisorPosPart_nonneg (-D))
  refine ⟨⟨f, g, fun P => ?_⟩⟩
  rw [hf, hg]
  simp only [Finsupp.coe_add, Pi.add_apply, divisorPosPart_apply,
    Finsupp.coe_neg, Pi.neg_apply]
  omega

/-- Exact composition into the existing child, from three independent
dimension statements about the actual Riemann–Roch subspaces. -/
theorem polarPresentation_of_riemannChildren
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hFinite : ∀ A : Divisor M, FiniteDimensional ℚ (riemannRochSpace M hDVR A))
    (hUpper : ∀ A : Divisor M, (riemannEll M hDVR A : ℤ) ≤
      max 0 (divisorDegree M A + (riemannEll M hDVR 0 : ℤ)))
    (hRiemann : ∃ g0 N0 : ℤ, ∀ A : Divisor M, N0 ≤ divisorDegree M A →
      (riemannEll M hDVR A : ℤ) = divisorDegree M A - g0)
    (D : Divisor M) : Nonempty (PolarPresentation M hDVR D) :=
  polarPresentation_of_largeEffectivePolarRealization M hDVR
    (largeEffectivePolarRealization_of_riemannChildren M hDVR hFinite hUpper hRiemann) D

end AbcAdaptation.Tripod.Fermat.Proper
