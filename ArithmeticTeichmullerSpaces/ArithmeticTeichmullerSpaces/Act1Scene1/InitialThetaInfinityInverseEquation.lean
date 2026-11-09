import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.GenericPoint

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the inverse-coordinate chart of the actual elliptic function field.
fidelity: the same generic point satisfies the transformed Weierstrass equation;
its second inverse coordinate is integral over the first-coordinate polynomial base.
Original proofs; no reference implementation copied.
boundary: this does not identify the normalization fiber with a projective cusp.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open WeierstrassCurve Polynomial
open scoped Classical

universe u
noncomputable section

/--
The inverse Weierstrass chart identity in a field.  Here `u = x⁻¹` and
`v = y x⁻²`; the only input is the original affine Weierstrass equation.
-/
theorem inverseCoordinateEquation_of_weierstrass
    {K : Type u} [Field K]
    {a₁ a₂ a₃ a₄ a₆ x y : K}
    (hEq : y ^ 2 + a₁ * x * y + a₃ * y =
      x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hx : x ≠ 0) :
    let u := x⁻¹
    let v := y * (x⁻¹) ^ 2
    v ^ 2 = u * (1 + a₂ * u + a₄ * u ^ 2 + a₆ * u ^ 3 - a₁ * v - a₃ * u * v) := by
  dsimp
  field_simp [hx]
  linear_combination hEq

/-- The second inverse coordinate is integral over the polynomial base in the first.
The witness is the displayed monic quadratic, without any smoothness hypothesis. -/
theorem isIntegral_secondInverseCoordinate_of_equation
    {k Ω : Type*} [CommRing k] [CommRing Ω] [Nontrivial Ω] [Algebra k Ω]
    {a₁ a₂ a₃ a₄ a₆ : k} {u v : Ω}
    (hEq : v ^ 2 = u *
      (1 + algebraMap k Ω a₂ * u + algebraMap k Ω a₄ * u ^ 2
        + algebraMap k Ω a₆ * u ^ 3 - algebraMap k Ω a₁ * v
        - algebraMap k Ω a₃ * u * v)) :
    IsIntegral (Algebra.adjoin k {u}) v := by
  let B : Subalgebra k Ω := Algebra.adjoin k {u}
  let U : B := ⟨u, Algebra.self_mem_adjoin_singleton k u⟩
  let b : B := algebraMap k B a₁ * U + algebraMap k B a₃ * U ^ 2
  let c : B := U + algebraMap k B a₂ * U ^ 2
    + algebraMap k B a₄ * U ^ 3 + algebraMap k B a₆ * U ^ 4
  change IsIntegral B v
  refine ⟨(X ^ 2 + C b * X - C c : B[X]), ?_, ?_⟩
  · simpa only [sub_eq_add_neg, map_neg] using
      (Polynomial.isMonicOfDegree_add_add_two b (-c)).monic
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    change v ^ 2 +
      (algebraMap k Ω a₁ * u + algebraMap k Ω a₃ * u ^ 2) * v -
        (u + algebraMap k Ω a₂ * u ^ 2 + algebraMap k Ω a₄ * u ^ 3
          + algebraMap k Ω a₆ * u ^ 4) = 0
    linear_combination hEq


namespace WeierstrassInverseChart

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

private abbrev ΩE (E : WeierstrassCurve k) := Genuine.Ω E

def firstCoordinate : ΩE E := (Genuine.xG E)⁻¹
def secondCoordinate : ΩE E := Genuine.yG E * ((Genuine.xG E)⁻¹) ^ 2

/-- The actual generic point supplies the inverse-chart equation. -/
theorem equation :
    secondCoordinate E ^ 2 =
      firstCoordinate E *
        (1 + algebraMap k (ΩE E) E.a₂ * firstCoordinate E
          + algebraMap k (ΩE E) E.a₄ * firstCoordinate E ^ 2
          + algebraMap k (ΩE E) E.a₆ * firstCoordinate E ^ 3
          - algebraMap k (ΩE E) E.a₁ * secondCoordinate E
          - algebraMap k (ΩE E) E.a₃ * firstCoordinate E * secondCoordinate E) := by
  have hPoint :
      (E⁄(ΩE E)).toAffine.Equation (Genuine.xG E) (Genuine.yG E) := by
    exact (Genuine.equation_xF_yF E).baseChange
      (IsScalarTower.toAlgHom k E.toAffine.FunctionField (ΩE E))
  rw [Affine.equation_iff] at hPoint
  have hEq :
      (Genuine.yG E) ^ 2
          + algebraMap k (ΩE E) E.a₁ * Genuine.xG E * Genuine.yG E
          + algebraMap k (ΩE E) E.a₃ * Genuine.yG E =
        (Genuine.xG E) ^ 3
          + algebraMap k (ΩE E) E.a₂ * (Genuine.xG E) ^ 2
          + algebraMap k (ΩE E) E.a₄ * Genuine.xG E
          + algebraMap k (ΩE E) E.a₆ := by
    simpa using hPoint
  exact inverseCoordinateEquation_of_weierstrass hEq
    (Genuine.transcendental_xG E).ne_zero

/-- The actual second inverse coordinate lies in the integral closure of `k[u]`. -/
theorem secondCoordinate_isIntegral :
    IsIntegral (Algebra.adjoin k {firstCoordinate E}) (secondCoordinate E) :=
  isIntegral_secondInverseCoordinate_of_equation (equation E)

end WeierstrassInverseChart

end
end JoshiTeich.Act1Scene1
