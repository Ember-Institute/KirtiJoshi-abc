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

end LocalCardinality

end

end JoshiTeich.Act1Scene1
