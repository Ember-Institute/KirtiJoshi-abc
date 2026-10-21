/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Orbifold.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `a772c5e73c0f632a34d1c866063e72f388f9352b`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: the source's 2026 iut contributors notice and Apache-2.0 license
were reviewed before copying; the notice is retained below.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing` and
`ss:theta-data-fixing2` (the once-punctured elliptic curve and torsion field).
fidelity: extracted the transcendental-x-coordinate proof only; added proofs that the
actual generic point lies outside the image of constant-field rational points.
boundary: Scene1/Derived. No orbicurve, core, or theta-root existence law is assumed.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Basic

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] (E : WeierstrassCurve k)

/-- The coordinate `x` of the generic point is transcendental over `k`. -/
lemma transcendental_xG [CharZero k] [E.IsElliptic] : Transcendental k (xG E) := by
  rintro ⟨p, hp, h⟩
  have hx : aeval (xF E) p = algebraMap k[X] E.toAffine.FunctionField p := by
    have hX : algebraMap k[X] E.toAffine.FunctionField Polynomial.X = xF E := by
      rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing]
      rfl
    rw [← hX, aeval_algebraMap_apply, aeval_X_left_apply]
  have h' : ιF E (algebraMap k[X] E.toAffine.FunctionField p) = 0 := by
    rw [← hx, ← Polynomial.aeval_algHom_apply]
    exact h
  have hinj : Function.Injective (algebraMap k[X] E.toAffine.CoordinateRing) := by
    intro p q h
    have h' : (p - q) • (1 : E.toAffine.CoordinateRing) + (0 : k[X]) •
        Affine.CoordinateRing.mk E.toAffine Polynomial.X = 0 := by
      rw [zero_smul, add_zero, sub_smul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (Affine.CoordinateRing.smul_basis_eq_zero h').1
  have h'' := (ιF E).injective (h'.trans (map_zero _).symm)
  rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing] at h''
  refine hp (hinj ?_)
  rw [map_zero]
  exact IsFractionRing.injective E.toAffine.CoordinateRing E.toAffine.FunctionField
    (h''.trans (map_zero _).symm)

/-- In characteristic zero the Galois base is the actual `x`-coordinate field. -/
lemma baseField_eq_xLine [CharZero k] : baseField E = xLine E := by
  have : Algebra.IsSeparable (xLine E) (Ω E) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  change (perfectClosure (xLine E) (Ω E)).restrictScalars k = xLine E
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.restrictScalars_bot_eq_self]

lemma xG_ne_algebraMap [CharZero k] [E.IsElliptic] (c : k) :
    xG E ≠ algebraMap k (Ω E) c := by
  intro h
  apply transcendental_xG E
  rw [h]
  exact isAlgebraic_algebraMap c

/-- The generic point cannot be replaced by a constant-field rational point. -/
theorem genericPoint_ne_base [CharZero k] [E.IsElliptic] (T : E.toAffine.Point) :
    genericPoint E ≠ base E T := by
  rcases T with _ | ⟨x, y, hxy⟩
  · intro h
    change Affine.Point.some _ _ _ = 0 at h
    cases h
  · intro h
    change Affine.Point.some (xG E) (yG E) _ =
      Affine.Point.some (algebraMap k (Ω E) x) (algebraMap k (Ω E) y) _ at h
    exact xG_ne_algebraMap E x (Affine.Point.some.inj h).1

lemma genericPoint_not_mem_range_base [CharZero k] [E.IsElliptic] :
    genericPoint E ∉ Set.range (base E) := by
  rintro ⟨T, hT⟩
  exact genericPoint_ne_base E T hT.symm

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
