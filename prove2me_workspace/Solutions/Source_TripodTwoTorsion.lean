/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/TwoTorsion.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve
open scoped Classical

/-- The Legendre curve has the four rational `2`-torsion points at infinity and at
`(0,0)`, `(1,0)`, and `(λ,0)`. -/
theorem card_torsionBy_two {K : Type*} [Field K] [NeZero (2 : K)] (l : K)
    [(legendre l).IsElliptic] (h0 : l ≠ 0) (h1 : l ≠ 1) :
    Nat.card ↥(AddSubgroup.torsionBy (legendre l).toAffine.Point ((2 : ℕ) : ℤ)) = 4 := by
  let P₀ : (legendre l).toAffine.Point := .some 0 0
    (Affine.equation_iff_nonsingular.mp (legendre_equation_zero l))
  let P₁ : (legendre l).toAffine.Point := .some 1 0
    (Affine.equation_iff_nonsingular.mp (legendre_equation_one l))
  let Pparam : (legendre l).toAffine.Point := .some l 0
    (Affine.equation_iff_nonsingular.mp (legendre_equation_self l))
  have hset : ((AddSubgroup.torsionBy (legendre l).toAffine.Point ((2 : ℕ) : ℤ)) :
      Set (legendre l).toAffine.Point) = {0, P₀, P₁, Pparam} := by
    ext P
    rw [SetLike.mem_coe, AddSubgroup.torsionBy.nsmul_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hP
      cases P with
      | zero => exact Or.inl rfl
      | some x y hxy =>
        have hy := (two_nsmul_some_eq_zero_iff l hxy).mp hP
        subst y
        rcases legendre_equation_y_zero l ((Affine.nonsingular_iff _ _).mp hxy).1 with hx | hx | hx
        · subst x
          exact Or.inr (Or.inl rfl)
        · subst x
          exact Or.inr (Or.inr (Or.inl rfl))
        · subst x
          exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact nsmul_zero 2
      · exact two_nsmul_some_zero l _
      · exact two_nsmul_some_zero l _
      · exact two_nsmul_some_zero l _
  have h₀₁ : P₀ ≠ P₁ := by
    intro h
    simp only [P₀, P₁, Affine.Point.some.injEq] at h
    exact zero_ne_one h.1
  have h0param : P₀ ≠ Pparam := by
    intro h
    simp only [P₀, Pparam, Affine.Point.some.injEq] at h
    exact h0 h.1.symm
  have h1param : P₁ ≠ Pparam := by
    intro h
    simp only [P₁, Pparam, Affine.Point.some.injEq] at h
    exact h1 h.1.symm
  have hinfty : (0 : (legendre l).toAffine.Point) ∉ ({P₀, P₁, Pparam} : Set _) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨(Affine.Point.some_ne_zero _).symm, (Affine.Point.some_ne_zero _).symm,
      (Affine.Point.some_ne_zero _).symm⟩
  have hfirst : P₀ ∉ ({P₁, Pparam} : Set _) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h₀₁, h0param⟩
  change Nat.card ↥((AddSubgroup.torsionBy (legendre l).toAffine.Point ((2 : ℕ) : ℤ)) :
    Set (legendre l).toAffine.Point) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem hinfty,
    Set.ncard_insert_of_notMem hfirst, Set.ncard_pair h1param]

/-- The curve of a tripod point has four points killed by multiplication by `2`. -/
theorem two_torsion_curveOf (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy (curveOf x h3 h5).E.toAffine.Point ((2 : ℕ) : ℤ)) := by
  haveI : (legendre (gen' x.1)).IsElliptic := legendre_gen'_isElliptic x
  exact (card_torsionBy_two (gen' x.1) (gen'_ne_zero x.2.1) (gen'_ne_one x.2.2)).ge

end AbcAdaptation.Tripod
