import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraNorm

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-GENERAL-ALGEBRA-NORM
source: the proved contracting completion norm identity, multiplicativity,
and inversion in the actual local completion.
fidelity: extends the identity to every nonzero scalar, including units and
expanding scalars. The raw completion norm is not made into an isometric
norm over Q_p. No new interface law is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open NumberField
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable (w : FinitePlace K) (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p)

theorem norm_algebraNorm_eq_completionNorm
    (x : completionAt K w) (hx : x ≠ 0) :
    letI := padicAlgebra hw
    ‖Algebra.norm ℚ_[p] x‖ = ‖x‖ := by
  letI := padicAlgebra hw
  letI : Module.Finite ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  rcases lt_trichotomy ‖x‖ 1 with h | h | h
  · exact norm_algebraNorm_eq_completionNorm_of_contracting w hw x hx h
  · letI : CharZero (completionAt K w) :=
      charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
    have hp0 : (p : completionAt K w) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hcast : ((p : K) : completionAt K w) = (p : completionAt K w) :=
      map_natCast (FinitePlace.embedding w.maximalIdeal) p
    have hp1 : ‖(p : completionAt K w)‖ < 1 := by
      rw [← hcast]
      exact norm_natCast_prime_lt_one hw
    have ha := norm_algebraNorm_eq_completionNorm_of_contracting w hw
      (p : completionAt K w) hp0 hp1
    have hb := norm_algebraNorm_eq_completionNorm_of_contracting w hw
      ((p : completionAt K w) * x) (mul_ne_zero hp0 hx) (by simpa [norm_mul, h] using hp1)
    rw [map_mul, norm_mul, norm_mul, ha] at hb
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hp0) hb
  · have hi := norm_algebraNorm_eq_completionNorm_of_contracting w hw x⁻¹
      (inv_ne_zero hx) (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h)
    have hm : ‖Algebra.norm ℚ_[p] x‖ * ‖Algebra.norm ℚ_[p] x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx, map_one, norm_one]
    rw [hi, norm_inv] at hm
    exact (mul_inv_eq_one₀ (norm_ne_zero_iff.mpr hx)).mp hm

end
end JoshiTeich.Act1Scene1.LocalCompletion
