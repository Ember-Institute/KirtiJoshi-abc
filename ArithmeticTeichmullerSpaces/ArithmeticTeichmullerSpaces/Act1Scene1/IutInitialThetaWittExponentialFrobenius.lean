import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialMultiplication
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenRadiusDynamics

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EXPONENTIAL-FROBENIUS
source: Joshi II `pr:teichmuller-lift-A`, recognition of multiplicative
formal-group periods inside the full Frobenius eigenspace.
fidelity: actual completed Frobenius transports the convergent exponential
from rho to rho^p. For any element of the entire original phi=p space,
the concrete smallness bound N_rho(z)<rho^2 ensures both exponentials
converge and gives phi(exp(z_rho))=exp(z_{rho^p})^p.
Every full eigen element can be brought into this domain by an actual
p-power scalar multiple, using the original coordinate norm law.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the original full eigenspace is retained.
Teichmuller recognition, exp/log inversion and full period representation
are not assumed or asserted. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittExponentialFrobenius

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialCoefficients InitialThetaWittExponentialSeries
open InitialThetaWittExponentialMultiplication InitialThetaWittEigenRadiusDynamics
open InitialThetaWittRhoFrobeniusCompletion InitialThetaWittRhoFrobeniusEquiv
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem frobenius_completedPadicMap (ρ : Radius) (a : Padic (Arithmetic.residueChar w.1)) :
    completedEquiv D w ρ (completedPadicMap D w ρ a) =
      completedPadicMap D w (poweredRadius D w ρ) a := by
  have h := InitialThetaWittAllRadiusFrobenius.evaluate_frobenius D w ρ (commonPadicMap D w a)
  rw [frobenius_padic, evaluate_padic, evaluate_padic] at h
  exact h.symm

theorem frobenius_term (ρ : Radius) (x : Ring D w ρ) (n : ℕ) :
    completedEquiv D w ρ (term D w ρ x n) =
      term D w (poweredRadius D w ρ) (completedEquiv D w ρ x) n := by
  rw [term, map_mul, map_pow, frobenius_completedPadicMap, term]

theorem norm_frobenius_lt (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    ‖completedEquiv D w ρ x‖ < (poweredRadius D w ρ).val.toReal := by
  rw [completedEquiv_apply, completedHom_norm]
  change ‖x‖ ^ Arithmetic.residueChar w.1 < (ρ.val ^ Arithmetic.residueChar w.1).toReal
  rw [ENNReal.toReal_pow]
  exact pow_lt_pow_left₀ hx (norm_nonneg x) (Arithmetic.residueChar_prime w.1).ne_zero

theorem frobenius_exp (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    completedEquiv D w ρ (exp D w ρ x) =
      exp D w (poweredRadius D w ρ) (completedEquiv D w ρ x) := by
  have h : HasSum (fun n : ℕ => completedEquiv D w ρ (term D w ρ x n))
      (completedEquiv D w ρ (exp D w ρ x)) :=
    (hasSum_exp D w ρ x hx).map (completedEquiv D w ρ).toAddMonoidHom
      (completedEquiv_continuous D w ρ)
  simp only [frobenius_term] at h
  exact h.unique (hasSum_exp D w (poweredRadius D w ρ) _ (norm_frobenius_lt D w ρ x hx))

theorem eigen_frobenius_coordinate (ρ : Radius) (z : Eigen D w) :
    completedEquiv D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ z.val) =
      Arithmetic.residueChar w.1 •
        InitialThetaWittAllRadiusCompletion.evaluate D w (poweredRadius D w ρ) z.val := by
  rw [← InitialThetaWittAllRadiusFrobenius.evaluate_frobenius, z.property,
    evaluate_smul, Nat.cast_smul_eq_nsmul]

theorem eigen_norm_lt (ρ : Radius) (z : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val < ρ.val.toReal ^ 2) :
    ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ z.val‖ < ρ.val.toReal := by
  have hr := radius_toReal_pos ρ
  have hr1 : ρ.val.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
        ρ.property.2
  exact hz.trans (by nlinarith)

theorem eigen_powered_norm_lt (ρ : Radius) (z : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val < ρ.val.toReal ^ 2) :
    ‖InitialThetaWittAllRadiusCompletion.evaluate D w (poweredRadius D w ρ) z.val‖ <
      (poweredRadius D w ρ).val.toReal := by
  change InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w (poweredRadius D w ρ) z.val < _
  rw [coordinate_powered_eq]
  apply (div_lt_iff₀ (radius_toReal_pos (poweredRadius D w ρ))).mpr
  have h := pow_lt_pow_left₀ hz
    (norm_nonneg (InitialThetaWittAllRadiusCompletion.evaluate D w ρ z.val))
    (Arithmetic.residueChar_prime w.1).ne_zero
  have he : (ρ.val.toReal ^ 2) ^ Arithmetic.residueChar w.1 =
      (poweredRadius D w ρ).val.toReal * (poweredRadius D w ρ).val.toReal := by
    change _ = (ρ.val ^ Arithmetic.residueChar w.1).toReal *
      (ρ.val ^ Arithmetic.residueChar w.1).toReal
    rw [ENNReal.toReal_pow, ← pow_two, ← pow_mul, ← pow_mul, Nat.mul_comm 2]
  exact h.trans_eq he

theorem eigen_frobenius_exp (ρ : Radius) (z : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val < ρ.val.toReal ^ 2) :
    completedEquiv D w ρ
      (exp D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ z.val)) =
      exp D w (poweredRadius D w ρ)
        (InitialThetaWittAllRadiusCompletion.evaluate D w (poweredRadius D w ρ) z.val) ^
          Arithmetic.residueChar w.1 := by
  rw [frobenius_exp D w ρ _ (eigen_norm_lt D w ρ z hz), eigen_frobenius_coordinate,
    exp_nsmul D w _ _ (eigen_powered_norm_lt D w ρ z hz)]

theorem exists_prime_pow_smul_small (ρ : Radius) (z : Eigen D w) : ∃ k : ℕ,
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val <
        ρ.val.toReal ^ 2 := by
  have hr1 : ρ.val.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
        ρ.property.2
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hr1).mul_const
    (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val)
  rw [zero_mul] at h
  obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds (pow_pos (radius_toReal_pos ρ) 2))).exists
  refine ⟨k, ?_⟩
  change InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
    (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z.val) < _
  rw [InitialThetaWittPadicScalarNorm.coordinateSeminorm_smul, map_pow, map_natCast, norm_pow,
    InitialThetaWittPadicScalarContinuity.norm_completed_prime]
  exact hk

end
end JoshiTeich.Act1Scene1.InitialThetaWittExponentialFrobenius
