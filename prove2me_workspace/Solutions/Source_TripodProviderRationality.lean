/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 10e40d2e52a8e7220c2a90ff1595f5b385f987ef
Original path Iut/Tripod/CurveFacts.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Solutions.Source_TripodUnramifiedBase

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

/-- The field of the actual Legendre curve contains a square root of `−1`. -/
theorem sqrt_neg_one_curveOf (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    IsSquare (-1 : (curveOf x h3 h5).F) := by
  let root : (curveOf x h3 h5).F :=
    ⟨sqrtNegOne, IntermediateField.subset_adjoin ℚ _
      (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))⟩
  refine ⟨root, Subtype.ext ?_⟩
  change (-1 : Qbar) = sqrtNegOne * sqrtNegOne
  rw [← sq, sqrtNegOne_sq]

private theorem two_torsion_coords (x : Pt) (a b : Qbar)
    (hab : (legendre x.1).toAffine.Nonsingular a b)
    (hQ : 2 • Point.some a b hab = 0) : a ∈ fieldOf' x.1 ∧ b ∈ fieldOf' x.1 := by
  have hb := (two_nsmul_some_eq_zero_iff x.1 hab).mp hQ
  subst b
  rcases legendre_equation_y_zero x.1 ((Affine.nonsingular_iff _ _).mp hab).1 with rfl | rfl | rfl
  · exact ⟨zero_mem _, zero_mem _⟩
  · exact ⟨one_mem _, zero_mem _⟩
  · exact ⟨mem_fieldOfExtended_self _, zero_mem _⟩

private theorem three_torsion_coords (x : Pt) (a b : Qbar)
    (hab : (legendre x.1).toAffine.Nonsingular a b)
    (hQ : 3 • Point.some a b hab = 0) : a ∈ fieldOf' x.1 ∧ b ∈ fieldOf' x.1 :=
  ⟨torsionCoords_three_subset_fieldOf' x.1 (mem_torsionCoords hQ (Set.mem_insert _ _)),
    torsionCoords_three_subset_fieldOf' x.1
      (mem_torsionCoords hQ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩

private theorem torsion_mem_range (x : Pt) {n : ℕ}
    (hcoords : ∀ (a b : Qbar) (hab : (legendre x.1).toAffine.Nonsingular a b),
      n • Point.some a b hab = 0 → a ∈ fieldOf' x.1 ∧ b ∈ fieldOf' x.1)
    (Q : (Affine.baseChange (legendre (gen' x.1)) Qbar).Point) (hQ : n • Q = 0) :
    Q ∈ (Point.baseChange (W' := legendre (gen' x.1)) (fieldOf' x.1) Qbar).range := by
  cases Q with
  | zero => exact zero_mem _
  | some a b hab =>
    have hbase : Affine.baseChange (legendre (gen' x.1)) Qbar = legendre x.1 :=
      legendre_baseChange (L := Qbar) (gen' x.1)
    have coords_of_model {W : Affine Qbar} (hW : W = (legendre x.1).toAffine)
        (habW : W.Nonsingular a b) (hQW : n • Point.some a b habW = 0) :
        a ∈ fieldOf' x.1 ∧ b ∈ fieldOf' x.1 := by
      subst W
      exact hcoords a b habW hQW
    obtain ⟨ha, hb⟩ := coords_of_model hbase hab hQ
    let aF : fieldOf' x.1 := ⟨a, ha⟩
    let bF : fieldOf' x.1 := ⟨b, hb⟩
    have habF : (Affine.baseChange (legendre (gen' x.1)) (fieldOf' x.1)).Nonsingular aF bF :=
      (Affine.baseChange_nonsingular (W := legendre (gen' x.1))
        (Algebra.ofId (fieldOf' x.1) Qbar).injective aF bF).mp hab
    exact ⟨Point.some aF bF habF, rfl⟩

/-- Every geometric point of the Legendre curve killed by `6` comes from its field of definition. -/
theorem six_torsion_rational_curveOf (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    SixTorsionRational (curveOf x h3 h5).F (curveOf x h3 h5).E (curveOf x h3 h5).Fbar := by
  intro Q hQ
  have h6 : (6 : ℕ) • Q = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hQ
  have h2 : 2 • (3 • Q) = 0 := by
    rw [smul_smul]
    exact h6
  have h3Q : 3 • (2 • Q) = 0 := by
    rw [smul_smul]
    exact h6
  let S := (Point.baseChange (W' := legendre (gen' x.1)) (fieldOf' x.1) Qbar).range
  have hmem : (3 : ℕ) • Q - (2 : ℕ) • Q ∈ S := S.sub_mem
    (torsion_mem_range x (two_torsion_coords x) (3 • Q) h2)
    (torsion_mem_range x (three_torsion_coords x) (2 • Q) h3Q)
  have hdiff : (3 : ℕ) • Q - (2 : ℕ) • Q = Q :=
    calc
      (3 : ℕ) • Q - (2 : ℕ) • Q = ((2 : ℕ) • Q + Q) - (2 : ℕ) • Q := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]
      _ = Q := add_sub_cancel_left _ _
  change Q ∈ S
  exact hdiff ▸ hmem

end AbcAdaptation.Tripod
