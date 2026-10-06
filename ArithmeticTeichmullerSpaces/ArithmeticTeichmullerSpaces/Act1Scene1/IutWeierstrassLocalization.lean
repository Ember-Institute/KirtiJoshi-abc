/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTorsionCardinality
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
source-id: IUT-COR312-WEIERSTRASS-LOCALIZATION
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/PointMap.lean` and
`refer/iut/Iut/Anabelian/LocalInputs.lean`.
fidelity: specializes the injective local additive map to actual Weierstrass points
using Mathlib's functorial affine-point map, then applies the existing torsion-cardinality
bound. Global rank-two torsion data and the local Tate uniformization remain inputs.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve

noncomputable section

section PointMap

variable {k K : Type*} [Field k] [Field K]
variable {E : WeierstrassCurve k} [E.IsElliptic]

open scoped Classical

/-- The point map induced by a field homomorphism, with the target curve base changed. -/
def iutWeierstrassPointMap (f : k →+* K) :
    E.toAffine.Point →+ (E.map f).toAffine.Point := by
  letI := f.toAlgebra
  exact Affine.Point.map (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

lemma iutWeierstrassPointMap_injective (f : k →+* K) :
    Function.Injective (iutWeierstrassPointMap (E := E) f) := by
  letI := f.toAlgebra
  exact Affine.Point.map_injective
    (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

/-- The concrete localization map on points for a chosen global torsion basis. -/
def iutWeierstrassTorsionLocalMap {ell : ℕ}
    (f : k →+* K)
    (T : IutGlobalTorsionBasis E.toAffine.Point ell) :
    IutTorsionLocalMap T (E.map f).toAffine.Point where
  toLocal := iutWeierstrassPointMap (E := E) f
  injective := iutWeierstrassPointMap_injective (E := E) f

end PointMap

section LocalCardinality

variable {k K : Type*} [Field k] [NormedField K]
variable {E : WeierstrassCurve k} [E.IsElliptic]

open scoped Classical

/-- A rank-two global torsion basis gives the local `ell²` lower bound under
Weierstrass base change and a Tate quotient uniformization. -/
theorem iutWeierstrass_local_torsion_card_lower_bound
    {ell : ℕ} (f : k →+* K)
    (T : IutGlobalTorsionBasis E.toAffine.Point ell)
    (S : IutTateQuotientUniformization K ((E.map f).toAffine.Point))
    (hEll : 0 < ell) :
    ell * ell ≤ Nat.card ↥(iutTorsion (E.map f).toAffine.Point ell) :=
  IutTorsionLocalMap.card_localTorsion_lower_bound T
    (iutWeierstrassTorsionLocalMap (E := E) f T) S hEll

/-- Any global lower bound on `ell`-torsion transfers through Weierstrass base change.
The map on points is injective, and the target torsion is finite by the Tate quotient. -/
theorem iutWeierstrass_local_torsion_card_lower_bound_of_global_card
    {ell : ℕ} (f : k →+* K)
    (S : IutTateQuotientUniformization K ((E.map f).toAffine.Point))
    (hEll : 0 < ell)
    (hGlobal : ell * ell ≤ Nat.card ↥(iutTorsion E.toAffine.Point ell)) :
    ell * ell ≤ Nat.card ↥(iutTorsion (E.map f).toAffine.Point ell) := by
  letI : NeZero ell := ⟨Nat.ne_of_gt hEll⟩
  haveI : Finite ↥(iutTorsion (E.map f).toAffine.Point ell) := S.finite_torsion
  let pointMap := iutWeierstrassPointMap (E := E) f
  have hmem : ∀ P : ↥(iutTorsion E.toAffine.Point ell),
      pointMap P.1 ∈ iutTorsion (E.map f).toAffine.Point ell := by
    intro P
    have hP := P.2
    rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
    rw [← map_nsmul, hP, map_zero]
  refine hGlobal.trans (Nat.card_le_card_of_injective
    (fun P : ↥(iutTorsion E.toAffine.Point ell) =>
      (⟨pointMap P.1, hmem P⟩ : ↥(iutTorsion (E.map f).toAffine.Point ell))) ?_)
  intro P Q h
  apply Subtype.ext
  exact iutWeierstrassPointMap_injective (E := E) f (congrArg Subtype.val h)

/-- Four global rational `2`-torsion points force a square root of the Tate parameter
after localization. This is the square-root input used by the IUT `2 ell`-root argument. -/
theorem iutWeierstrass_exists_square_root_of_global_two_torsion
    (f : k →+* K)
    (S : IutTateQuotientUniformization K ((E.map f).toAffine.Point))
    (htwo : 2 * 2 ≤ Nat.card ↥(iutTorsion E.toAffine.Point 2)) :
    ∃ s : K, s ^ 2 = (S.q : K) := by
  have hLocal := iutWeierstrass_local_torsion_card_lower_bound_of_global_card
    (E := E) f S (ell := 2) (by omega) htwo
  obtain ⟨u, m, hu⟩ := S.exists_root_class_values_of_torsion_card (ell := 2)
    (by omega) hLocal
  exact IutQRootExistence.exists_pow_eq_of_root_class_of_nonzero
    (show 0 < 2 by omega) (Units.ne_zero S.q) hu

end LocalCardinality

end

end JoshiTeich.Act1Scene1
