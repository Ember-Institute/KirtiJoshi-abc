import ArithmeticTeichmullerSpaces.Act1Scene1.AdjoinRootEtaleLocus
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the original Weierstrass equation and Mathlib's prime etale locus.
fidelity: the actual x-projection is etale precisely off the vanishing of
2Y+a₁X+a₃. This branch equation squares to the two-torsion polynomial.
boundary: Scene1/Derived. This concerns the ordinary coordinate double cover;
the orbicurve realization and full producer remain open.
-/

namespace JoshiTeich.Act1Scene1.WeierstrassBranchLocus

open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- The actual derivative of the monic Weierstrass polynomial in Y. -/
def branchElement : W.CoordinateRing :=
  2 * Affine.CoordinateRing.mk W X +
    algebraMap R[X] W.CoordinateRing (C W.a₁ * X + C W.a₃)

theorem mk_derivative : AdjoinRoot.mk W.polynomial W.polynomial.derivative = branchElement W := by
  have hd : W.polynomial.derivative = 2 * X + C (C W.a₁ * X + C W.a₃) := by
    simp only [Affine.polynomial, derivative_sub, derivative_add, derivative_mul,
      derivative_pow, derivative_C, derivative_X, zero_mul, mul_one,
      zero_add, sub_zero, Nat.reduceSub, pow_one, Nat.cast_ofNat, map_ofNat]
  rw [hd, map_add, map_mul, map_ofNat]
  rfl

theorem isEtaleAt_iff (q : Ideal W.CoordinateRing) [q.IsPrime] :
    Algebra.IsEtaleAt R[X] q ↔ branchElement W ∉ q := by
  rw [← mk_derivative]
  exact AdjoinRootEtaleLocus.isEtaleAt_iff_derivative_not_mem
    W.polynomial W.monic_polynomial q

theorem etaleLocus_eq_basicOpen :
    Algebra.etaleLocus R[X] W.CoordinateRing = PrimeSpectrum.basicOpen (branchElement W) := by
  ext q
  exact isEtaleAt_iff W q.asIdeal

theorem branchElement_sq : branchElement W ^ 2 =
    algebraMap R[X] W.CoordinateRing W.twoTorsionPolynomial.toPoly := by
  have hy : Affine.CoordinateRing.mk W X ^ 2 =
      (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) • (1 : W.CoordinateRing) +
        (-(C W.a₁ * X + C W.a₃)) • Affine.CoordinateRing.mk W X := by
    simpa [pow_two] using Affine.CoordinateRing.smul_basis_mul_Y (W' := W) 0 1
  unfold branchElement
  simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly, b₂, b₄, b₆,
    map_add, map_mul, map_neg, map_pow, map_ofNat, Algebra.smul_def, mul_one] at hy ⊢
  linear_combination 4 * hy

/-- The branch equation is equivalent to the pulled-back two-torsion equation at every prime. -/
theorem branchElement_mem_iff (q : Ideal W.CoordinateRing) [q.IsPrime] :
    branchElement W ∈ q ↔ W.twoTorsionPolynomial.toPoly ∈ q.under R[X] := by
  change _ ↔ algebraMap R[X] W.CoordinateRing W.twoTorsionPolynomial.toPoly ∈ q
  rw [← branchElement_sq]
  exact (Ideal.IsPrime.pow_mem_iff_mem inferInstance 2 (by decide)).symm

theorem isEtaleAt_iff_twoTorsion_not_mem (q : Ideal W.CoordinateRing) [q.IsPrime] :
    Algebra.IsEtaleAt R[X] q ↔ W.twoTorsionPolynomial.toPoly ∉ q.under R[X] := by
  rw [isEtaleAt_iff, branchElement_mem_iff]

end
end JoshiTeich.Act1Scene1.WeierstrassBranchLocus
