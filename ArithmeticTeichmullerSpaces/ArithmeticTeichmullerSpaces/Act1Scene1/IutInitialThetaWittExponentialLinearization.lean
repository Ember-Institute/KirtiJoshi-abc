import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialMultiplication

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EXPONENTIAL-LINEARIZATION
source: Joshi II `pr:teichmuller-lift-A`, multiplicative-formal-group
periods; the first derivative of the convergent exponential at zero.
fidelity: bounds the actual exponential remainder by (norm(x)/rho)^2.
The original p-power scalar norm then bounds the normalized remainder
by rho^k*(norm(x)/rho)^2 and proves convergence of the actual normalized
exponential differences to x. No derivative or inverse law is input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; all norms, scalar actions and completions are
the existing ones. Full period representation remains open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittExponentialLinearization

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialSeries InitialThetaWittExponentialMultiplication
open InitialThetaWittPadicScalarNorm InitialThetaWittPadicScalarContinuity
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem radius_toReal_lt_one (ρ : Radius) : ρ.val.toReal < 1 := by
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
      ρ.property.2

theorem term_one (ρ : Radius) (x : Ring D w ρ) : term D w ρ x 1 = x := by
  simp only [term, InitialThetaWittExponentialCoefficients.coefficient_one, map_one, pow_one, one_mul]

theorem hasSum_exp_remainder (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    HasSum (fun n : ℕ => term D w ρ x (n + 2)) (exp D w ρ x - 1 - x) := by
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, term_zero, term_one,
    sub_add_eq_sub_sub] using (hasSum_nat_add_iff' 2).mpr (hasSum_exp D w ρ x hx)

theorem norm_exp_remainder_le (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    ‖exp D w ρ x - 1 - x‖ ≤ (‖x‖ / ρ.val.toReal) ^ 2 := by
  have hs := hasSum_exp_remainder D w ρ x hx
  rw [← hs.tsum_eq]
  apply UltrametricLogTailBounds.norm_tsum_le_of_forall_le _ hs.summable _ (sq_nonneg _)
  intro n
  exact (norm_term_le D w ρ x (n + 2)).trans
    (pow_le_pow_of_le_one (div_nonneg (norm_nonneg x) (radius_toReal_pos ρ).le)
      ((div_lt_one (radius_toReal_pos ρ)).mpr hx).le (Nat.le_add_left 2 n))

theorem norm_prime_pow_smul (ρ : Radius) (x : Ring D w ρ) (k : ℕ) :
    ‖((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x‖ =
      ρ.val.toReal ^ k * ‖x‖ := by
  rw [norm_padic_smul, map_pow, map_natCast, norm_pow, norm_completed_prime]

theorem norm_prime_pow_inv_smul (ρ : Radius) (x : Ring D w ρ) (k : ℕ) :
    ‖((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ • x‖ =
      ‖x‖ / ρ.val.toReal ^ k := by
  have ha : (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k ≠ 0 :=
    pow_ne_zero k (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  apply (eq_div_iff (pow_pos (radius_toReal_pos ρ) k).ne').mpr
  have h := norm_prime_pow_smul D w ρ
    (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ • x) k
  rw [smul_inv_smul₀ ha] at h
  exact (mul_comm _ _).trans h.symm

theorem norm_prime_pow_smul_le (ρ : Radius) (x : Ring D w ρ) (k : ℕ) :
    ‖((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x‖ ≤ ‖x‖ := by
  rw [norm_prime_pow_smul]
  exact mul_le_of_le_one_left (norm_nonneg x)
    (pow_le_one₀ (radius_toReal_pos ρ).le (radius_toReal_lt_one ρ).le)

def quotient (ρ : Radius) (x : Ring D w ρ) (k : ℕ) : Ring D w ρ :=
  ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ •
    (exp D w ρ (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x) - 1)

theorem quotient_sub (ρ : Radius) (x : Ring D w ρ) (k : ℕ) :
    quotient D w ρ x k - x =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ •
        (exp D w ρ (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x) -
          1 - ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x) := by
  have ha : (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k ≠ 0 :=
    pow_ne_zero k (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  symm
  rw [smul_sub, inv_smul_smul₀ ha]
  rfl

theorem norm_quotient_sub_le (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) (k : ℕ) :
    ‖quotient D w ρ x k - x‖ ≤ ρ.val.toReal ^ k * (‖x‖ / ρ.val.toReal) ^ 2 := by
  rw [quotient_sub, norm_prime_pow_inv_smul]
  have h := norm_exp_remainder_le D w ρ _ ((norm_prime_pow_smul_le D w ρ x k).trans_lt hx)
  rw [norm_prime_pow_smul] at h
  calc
    _ ≤ ((ρ.val.toReal ^ k * ‖x‖) / ρ.val.toReal) ^ 2 / ρ.val.toReal ^ k :=
      div_le_div_of_nonneg_right h (pow_pos (radius_toReal_pos ρ) k).le
    _ = _ := by
      field_simp [(radius_toReal_pos ρ).ne', (pow_pos (radius_toReal_pos ρ) k).ne']
      <;> ring

theorem tendsto_quotient (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    Filter.Tendsto (quotient D w ρ x) Filter.atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (radius_toReal_pos ρ).le
    (radius_toReal_lt_one ρ)).mul_const ((‖x‖ / ρ.val.toReal) ^ 2)
  rw [zero_mul] at h
  exact squeeze_zero (fun k => norm_nonneg _) (norm_quotient_sub_le D w ρ x hx) h

end
end JoshiTeich.Act1Scene1.InitialThetaWittExponentialLinearization
