import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPadicScalarNorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-LOG-DENOMINATOR-BOUNDS
source: Joshi II `se:ff-rings` and the logarithmic Tate period in
`pr:teichmuller-lift-A/B`; the rho norms of the rational log coefficients.
fidelity: computes the actual image norm of 1/n as the reciprocal of
rho raised to v_p(n). For every radius, proves one polynomial bound
valid for every positive n, using p^v_p(n) <= n. No coefficient bound
is supplied by the caller. Original proofs; no reference code copied.
boundary: Scene1/Derived; convergence and actual Tate membership are
separate steps. No paper B or BK identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLogDenominatorBounds

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittScalarPrimeScaling
open InitialThetaWittPadicScalarNorm InitialThetaWittPadicScalarContinuity
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem integral_natCast_valuation (n : ℕ) :
    (n : PadicInt (Arithmetic.residueChar w.1)).valuation = padicValNat (Arithmetic.residueChar w.1) n := by
  simp only [PadicInt.valuation, PadicInt.coe_natCast, Padic.valuation_natCast, Int.toNat_natCast]

theorem norm_completed_natCast (ρ : Radius) (n : ℕ) (hn : n ≠ 0) :
    ‖(n : Completed D w ρ)‖ = ρ.val.toReal ^ padicValNat (Arithmetic.residueChar w.1) n := by
  have h := norm_integralMap D w ρ (n : PadicInt (Arithmetic.residueChar w.1))
    (Nat.cast_ne_zero.mpr hn)
  simpa only [map_natCast, integral_natCast_valuation] using h

theorem norm_inverse_natCast (ρ : Radius) (n : ℕ) (hn : n ≠ 0) :
    ‖completedPadicMap D w ρ (n : Padic (Arithmetic.residueChar w.1))⁻¹‖ =
      1 / ρ.val.toReal ^ padicValNat (Arithmetic.residueChar w.1) n := by
  have hnP : (n : Padic (Arithmetic.residueChar w.1)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hp : ρ.val.toReal ^ padicValNat (Arithmetic.residueChar w.1) n ≠ 0 :=
    pow_ne_zero _ (ENNReal.toReal_pos ρ.property.1.ne'
      (ρ.property.2.trans ENNReal.one_lt_top).ne).ne'
  have h := norm_completedPadicMap_mul_scalar D w ρ
    (n : Padic (Arithmetic.residueChar w.1))⁻¹ (n : Padic (Arithmetic.residueChar w.1))
  rw [inv_mul_cancel₀ hnP, map_one, norm_one, map_natCast, norm_completed_natCast D w ρ n hn] at h
  exact (eq_div_iff hp).mpr h.symm

theorem exists_polynomial_bound (ρ : Radius) :
    ∃ k : ℕ, ∀ n : ℕ, n ≠ 0 →
      ‖completedPadicMap D w ρ (n : Padic (Arithmetic.residueChar w.1))⁻¹‖ ≤ (n : ℝ) ^ k := by
  have hp1 : (1 : ℝ) < Arithmetic.residueChar w.1 := by
    exact_mod_cast (Arithmetic.residueChar_prime w.1).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (ρ.val.toReal)⁻¹ hp1
  refine ⟨k, fun n hn => ?_⟩
  rw [norm_inverse_natCast D w ρ n hn, one_div, ← inv_pow]
  calc
    _ ≤ ((Arithmetic.residueChar w.1 : ℝ) ^ k) ^ padicValNat (Arithmetic.residueChar w.1) n :=
      pow_le_pow_left₀ (inv_nonneg.mpr ENNReal.toReal_nonneg) hk.le _
    _ = ((Arithmetic.residueChar w.1 : ℝ) ^ padicValNat (Arithmetic.residueChar w.1) n) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (n : ℝ) ^ k := by
      apply pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg _) _) _ k
      exact_mod_cast (Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hn)
        (pow_padicValNat_dvd : Arithmetic.residueChar w.1 ^ padicValNat (Arithmetic.residueChar w.1) n ∣ n))

end
end JoshiTeich.Act1Scene1.InitialThetaWittLogDenominatorBounds
