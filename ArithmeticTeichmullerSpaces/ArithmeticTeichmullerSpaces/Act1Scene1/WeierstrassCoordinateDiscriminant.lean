import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Discriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's Weierstrass coordinate-ring basis, algebra trace and cubic discriminant.
fidelity: computes the discriminant of the actual Weierstrass coordinate basis
and proves that it is squarefree for an elliptic curve in characteristic zero.
boundary: Scene1/Derived. These are coordinate-ring invariants for the natural
normalization comparison. Surjectivity and the geometric producer remain open.
-/

namespace JoshiTeich.Act1Scene1.WeierstrassCoordinateDiscriminant

open WeierstrassCurve Polynomial
open scoped Classical
universe u
noncomputable section
variable {R : Type u} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- The trace of an element in the original polynomial basis `{1,Y}`. -/
theorem trace_smul_basis (p q : R[X]) :
    Algebra.trace R[X] W.CoordinateRing
        (p • (1 : W.CoordinateRing) + q • Affine.CoordinateRing.mk W X) =
      2 * p - q * (C W.a₁ * X + C W.a₃) := by
  simp_rw [Algebra.trace_eq_matrix_trace (Affine.CoordinateRing.basis W), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Affine.CoordinateRing.basis_zero, mul_one,
    Affine.CoordinateRing.basis_one, Affine.CoordinateRing.smul_basis_mul_Y, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← Affine.CoordinateRing.basis_zero,
    ← Affine.CoordinateRing.basis_one, Module.Basis.repr_self_apply, if_pos,
    one_ne_zero, ite_false, smul_eq_mul]
  simp only [if_false, if_true, zero_ne_one]
  ring

theorem trace_one : Algebra.trace R[X] W.CoordinateRing 1 = 2 := by
  simpa using trace_smul_basis W 1 0

theorem trace_Y : Algebra.trace R[X] W.CoordinateRing (Affine.CoordinateRing.mk W X) =
    -(C W.a₁ * X + C W.a₃) := by
  simpa using trace_smul_basis W 0 1

theorem trace_Y_sq : Algebra.trace R[X] W.CoordinateRing (Affine.CoordinateRing.mk W X ^ 2) =
    (C W.a₁ * X + C W.a₃) ^ 2 +
      2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
  have hsq : Affine.CoordinateRing.mk W X ^ 2 =
      (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) • (1 : W.CoordinateRing) +
        (-(C W.a₁ * X + C W.a₃)) • Affine.CoordinateRing.mk W X := by
    simpa [pow_two] using Affine.CoordinateRing.smul_basis_mul_Y (W' := W) 0 1
  rw [hsq, trace_smul_basis]
  ring

/-- The basis discriminant is the original curve's two-torsion polynomial. -/
theorem discr_basis : Algebra.discr R[X] (Affine.CoordinateRing.basis W) =
    W.twoTorsionPolynomial.toPoly := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    Affine.CoordinateRing.basis_zero, Affine.CoordinateRing.basis_one, one_mul, mul_one,
    ← pow_two]
  simp only [one_pow]
  rw [trace_one W, trace_Y W, trace_Y_sq W]
  simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly, b₂, b₄, b₆]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

theorem twoTorsionPolynomial_separable : E.twoTorsionPolynomial.toPoly.Separable := by
  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    change (4 : k) ≠ 0
    norm_num
  have hs : (E.twoTorsionPolynomial.toPoly.map (algebraMap k (AlgebraicClosure k))).Splits :=
    IsAlgClosed.splits _
  apply (Polynomial.nodup_aroots_iff_of_splits
    (E.twoTorsionPolynomial.ne_zero_of_a_ne_zero ha) hs).mp
  rw [Polynomial.aroots_def]
  rw [← Cubic.map_toPoly]
  exact (E.twoTorsionPolynomial.discr_ne_zero_iff_roots_nodup ha hs).mp
    (E.twoTorsionPolynomial_discr_ne_zero_of_isElliptic (isUnit_iff_ne_zero.mpr two_ne_zero))

theorem discr_basis_squarefree :
    Squarefree (Algebra.discr k[X] (Affine.CoordinateRing.basis E.toAffine)) := by
  rw [discr_basis]
  exact (twoTorsionPolynomial_separable E).squarefree

/-- A square factor of the actual basis discriminant must be a unit. -/
theorem index_isUnit_of_sq_dvd (d : k[X])
    (hd : d ^ 2 ∣ Algebra.discr k[X] (Affine.CoordinateRing.basis E.toAffine)) : IsUnit d :=
  discr_basis_squarefree E d (by simpa only [pow_two] using hd)

end
end JoshiTeich.Act1Scene1.WeierstrassCoordinateDiscriminant
