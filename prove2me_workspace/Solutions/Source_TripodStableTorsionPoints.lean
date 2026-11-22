/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/StableTwo.lean
-/
import Solutions.Source_TripodProviderRationality
import Solutions.Source_TripodTorsionBasis
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve
open scoped Classical

/-- The actual Legendre curve over its field of definition has two independent points of order
three. -/
theorem independent_three_torsion_curveOf (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) :
    ∃ P Q : (curveOf x h3 h5).E.toAffine.Point,
      3 • P = 0 ∧ 3 • Q = 0 ∧ P ≠ 0 ∧ Q ≠ 0 ∧ Q ≠ P ∧ Q ≠ -P := by
  let C := curveOf x h3 h5
  let V := Affine.baseChange C.E C.F
  let W := Affine.baseChange C.E C.Fbar
  change ∃ P Q : V.Point, 3 • P = 0 ∧ 3 • Q = 0 ∧ P ≠ 0 ∧ Q ≠ 0 ∧ Q ≠ P ∧ Q ≠ -P
  let φ : V.Point →+ W.Point := Affine.Point.baseChange (W' := C.E) C.F C.Fbar
  have hbase : W = (legendre x.1).toAffine := by
    change Affine.baseChange (legendre (gen' x.1)) Qbar = legendre x.1
    exact legendre_baseChange (L := Qbar) (gen' x.1)
  have hb : Nonempty (AddSubgroup.torsionBy W.Point 3 ≃+ (Fin 2 → ZMod 3)) := by
    rw [hbase]
    exact legendre_torsionBasis_three x
  obtain ⟨e⟩ := hb
  set P₀ : AddSubgroup.torsionBy W.Point 3 := e.symm ![1, 0] with hP₀
  set Q₀ : AddSubgroup.torsionBy W.Point 3 := e.symm ![0, 1] with hQ₀
  have hφ : Function.Injective φ :=
    Affine.Point.map_injective (W' := C.E) (Algebra.ofId C.F C.Fbar)
  have rational (R : W.Point) (hR : R ∈ AddSubgroup.torsionBy W.Point 6) : R ∈ φ.range :=
    six_torsion_rational_curveOf x h3 h5 R hR
  have lift (R : AddSubgroup.torsionBy W.Point 3) :
      ∃ T : V.Point, φ T = (R : W.Point) ∧ 3 • T = 0 := by
    have h3R : 3 • (R : W.Point) = 0 := AddSubgroup.torsionBy.nsmul_iff.mp R.2
    have h6R : (6 : ℕ) • (R : W.Point) = 0 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, ← smul_smul (2 : ℕ) (3 : ℕ), h3R, nsmul_zero]
    obtain ⟨T, hT⟩ := rational (R : W.Point) (AddSubgroup.torsionBy.nsmul_iff.mpr h6R)
    refine ⟨T, hT, hφ ?_⟩
    rw [map_nsmul φ, map_zero φ, hT]
    exact h3R
  obtain ⟨P, hP, hP3⟩ := lift P₀
  obtain ⟨Q, hQ, hQ3⟩ := lift Q₀
  refine ⟨P, Q, hP3, hQ3, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, map_zero φ] at hP
    have hzero : P₀ = 0 := Subtype.ext hP.symm
    rw [hP₀, AddEquiv.map_eq_zero_iff] at hzero
    exact absurd (congrFun hzero 0) (by decide)
  · intro h
    rw [h, map_zero φ] at hQ
    have hzero : Q₀ = 0 := Subtype.ext hQ.symm
    rw [hQ₀, AddEquiv.map_eq_zero_iff] at hzero
    exact absurd (congrFun hzero 1) (by decide)
  · intro h
    rw [h, hP] at hQ
    have heq : P₀ = Q₀ := Subtype.ext hQ
    rw [hP₀, hQ₀, e.symm.injective.eq_iff] at heq
    exact absurd (congrFun heq 0) (by decide)
  · intro h
    rw [h, map_neg φ, hP] at hQ
    have heq : -P₀ = Q₀ := Subtype.ext hQ
    rw [hP₀, hQ₀, ← map_neg, e.symm.injective.eq_iff] at heq
    exact absurd (congrFun heq 1) (by decide)

end AbcAdaptation.Tripod
