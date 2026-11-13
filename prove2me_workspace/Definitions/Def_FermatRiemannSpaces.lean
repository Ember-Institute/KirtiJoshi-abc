/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent adaptation of the L(A) definition in
Belyi/CurveField/RiemannRochSpace.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatCurveFieldResidue
import Definitions.Def_FermatCurveFieldZerosPoles
import Definitions.Def_FermatProperDivisorHeight
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- The actual Riemann–Roch subspace. The zero element is included
separately because normalized ord has the source's convention ord(0)=0. -/
def riemannRochSpace (M : Model N) (hDVR : PlacesDiscrete M)
    (A : Divisor M) : Submodule ℚ M.K := by
  letI : IsCurveField M.K := M.isCurveField
  exact {
    carrier := {f | f = 0 ∨ ∀ P : Place M.K, -A P ≤ ord M hDVR P f}
    zero_mem' := Or.inl rfl
    add_mem' := by
      rintro f g (rfl | hf) (rfl | hg)
      · simp
      · simpa using Or.inr hg
      · simpa using Or.inr hf
      by_cases hfg : f + g = 0
      · exact Or.inl hfg
      refine Or.inr fun P => ?_
      simp only [ord_eq_placeOrd] at hf hg ⊢
      exact (le_min (hf P) (hg P)).trans (P.min_le_ord_add hfg)
    smul_mem' := by
      rintro q f (rfl | hf)
      · simp
      by_cases h : q • f = 0
      · exact Or.inl h
      refine Or.inr fun P => ?_
      rw [Rat.smul_def] at h ⊢
      have hq : (q : M.K) ≠ 0 := left_ne_zero_of_mul h
      have hf0 : f ≠ 0 := right_ne_zero_of_mul h
      rw [ord_eq_placeOrd, P.ord_mul hq hf0, P.ord_ratCast, zero_add]
      simpa only [ord_eq_placeOrd] using hf P }

theorem mem_riemannRochSpace (M : Model N) (hDVR : PlacesDiscrete M)
    (A : Divisor M) (f : M.K) :
    f ∈ riemannRochSpace M hDVR A ↔
      f = 0 ∨ ∀ P : Place M.K, -A P ≤ ord M hDVR P f := Iff.rfl

theorem riemannRochSpace_mono (M : Model N) (hDVR : PlacesDiscrete M)
    {A B : Divisor M} (h : A ≤ B) :
    riemannRochSpace M hDVR A ≤ riemannRochSpace M hDVR B := by
  rintro f (rfl | hf)
  · exact Or.inl rfl
  exact Or.inr fun P => (neg_le_neg (h P)).trans (hf P)

/-- The actual rational dimension, not a freely specified genus function.
Every theorem that uses finrank as dimension also takes actual finiteness. -/
noncomputable def riemannEll (M : Model N) (hDVR : PlacesDiscrete M)
    (A : Divisor M) : ℕ := Module.finrank ℚ (riemannRochSpace M hDVR A)

theorem divisorDegree_add (M : Model N) (A B : Divisor M) :
    divisorDegree M (A + B) = divisorDegree M A + divisorDegree M B :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

@[simp] theorem divisorDegree_zero (M : Model N) :
    divisorDegree M (0 : Divisor M) = 0 := Finsupp.sum_zero_index

noncomputable def divisorDegreeHom (M : Model N) : Divisor M →+ ℤ where
  toFun := divisorDegree M
  map_zero' := divisorDegree_zero M
  map_add' := divisorDegree_add M

theorem divisorDegree_sub (M : Model N) (A B : Divisor M) :
    divisorDegree M (A - B) = divisorDegree M A - divisorDegree M B :=
  map_sub (divisorDegreeHom M) A B

@[simp] theorem divisorDegree_single (M : Model N) (P : Place M.K) (n : ℤ) :
    divisorDegree M (Finsupp.single P n) = n * P.degree :=
  Finsupp.sum_single_index
    (h := fun (Q : Place M.K) (m : ℤ) => m * (Q.degree : ℤ)) (zero_mul _)

theorem divisorDegree_nonneg (M : Model N) {A : Divisor M} (hA : 0 ≤ A) :
    0 ≤ divisorDegree M A :=
  Finset.sum_nonneg fun P _ => mul_nonneg (hA P) (Int.natCast_nonneg _)

/-- The finite positive part of an actual divisor. -/
noncomputable def divisorPosPart {M : Model N} (A : Divisor M) : Divisor M :=
  Finsupp.mapRange (fun n => max n 0) (by simp) A

theorem divisorPosPart_apply {M : Model N} (A : Divisor M) (P : Place M.K) :
    divisorPosPart A P = max (A P) 0 := Finsupp.mapRange_apply ..

theorem divisorPosPart_nonneg {M : Model N} (A : Divisor M) :
    0 ≤ divisorPosPart A := fun P => by simp [divisorPosPart_apply]

end AbcAdaptation.Tripod.Fermat.Proper
