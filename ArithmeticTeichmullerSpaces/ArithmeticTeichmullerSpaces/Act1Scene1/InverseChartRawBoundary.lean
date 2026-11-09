import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
A generic algebraic boundary certificate for the inverse Weierstrass chart.

For
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`,
the inverse coordinates `u = x⁻¹`, `v = y x⁻²` satisfy
`v² = u * (1 + a₂u + a₄u² + a₆u³ - a₁v - a₃uv)`.
Thus a prime containing `u` contains `v`.  The remaining input is the
actual closed-point certificate that `(u,v)` is maximal (equivalently, an
evaluation map to the residue field with this kernel).
-/

namespace JoshiTeich.Act1Scene1.InverseChartRawBoundary

universe u

variable {R : Type u} [CommRing R]
variable {a₁ a₂ a₃ a₄ a₆ u v : R}

/-- The right side of the transformed generic Weierstrass equation. -/
def inverseEquationRhs : R :=
  u * (1 + a₂ * u + a₄ * u ^ 2 + a₆ * u ^ 3 - a₁ * v - a₃ * u * v)

/--
A prime containing the inverse coordinate `u` also contains `v`, by the
transformed Weierstrass equation.
-/
theorem second_inverse_coordinate_mem_of_prime
    (hEq : v ^ 2 = inverseEquationRhs (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
      (a₄ := a₄) (a₆ := a₆) (u := u) (v := v))
    {P : Ideal R} (hP : P.IsPrime) (hu : u ∈ P) :
    v ∈ P := by
  apply hP.mem_of_pow_mem 2
  rw [hEq]
  simpa [inverseEquationRhs] using P.mul_mem_right _ hu

/--
An evaluation at the inverse-chart origin supplies the maximality part of
the boundary certificate.  In applications `e` is the residue evaluation
at `u = v = 0`.
-/
theorem boundary_isMaximal_of_eval
    {k : Type u} [Field k]
    (e : R →+* k) (he : Function.Surjective e)
    (hker : RingHom.ker e = Ideal.span ({u, v} : Set R)) :
    (Ideal.span ({u, v} : Set R)).IsMaximal := by
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective e he

/--
Generic inverse-chart boundary classification.  This is the directly
consumable certificate for an actual normalization prime: supply the
transformed equation and the maximality/evaluation certificate for `(u,v)`.
-/
theorem prime_eq_origin_of_inverse_equation
    (hEq : v ^ 2 = inverseEquationRhs (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
      (a₄ := a₄) (a₆ := a₆) (u := u) (v := v))
    (hBoundary : (Ideal.span ({u, v} : Set R)).IsMaximal)
    {P : Ideal R} (hP : P.IsPrime) (hu : u ∈ P) :
    P = Ideal.span ({u, v} : Set R) := by
  have hv : v ∈ P := second_inverse_coordinate_mem_of_prime hEq hP hu
  have hle : Ideal.span ({u, v} : Set R) ≤ P := by
    rw [Ideal.span_le]
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hu
    · exact (Set.mem_singleton_iff.mp hz) ▸ hv
  exact (hBoundary.eq_of_le hP.ne_top hle).symm

/- The evaluation form is convenient when the actual chart is presented by
an explicit residue map rather than by a precomputed maximality instance. -/
theorem prime_eq_origin_of_inverse_equation_of_eval
    {k : Type u} [Field k]
    (hEq : v ^ 2 = inverseEquationRhs (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
      (a₄ := a₄) (a₆ := a₆) (u := u) (v := v))
    (e : R →+* k) (he : Function.Surjective e)
    (hker : RingHom.ker e = Ideal.span ({u, v} : Set R))
    {P : Ideal R} (hP : P.IsPrime) (hu : u ∈ P) :
    P = Ideal.span ({u, v} : Set R) := by
  exact prime_eq_origin_of_inverse_equation hEq
    (boundary_isMaximal_of_eval e he hker) hP hu

end JoshiTeich.Act1Scene1.InverseChartRawBoundary
