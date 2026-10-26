import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialLinearization
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-LOG-EXP-INVERSE
source: Joshi II `pr:teichmuller-lift-A`, the multiplicative-formal-group
description of B^{phi=p} and the exact period sequence.
fidelity: the actual Iwasawa quotient of exp(x) is the normalized actual
exponential difference. Its two proved limits give log(exp(x))=x in the
original rho completion whenever norm(x)<rho. This proves exponential
injectivity there and recovers every sufficiently small full eigen
element from its exponential coordinate, without a representation law.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; only the stated left inverse is proved here.
The reverse identity on arbitrary principal units, Teichmuller recognition
and full period representation remain separate obligations. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLogExpInverse

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialSeries InitialThetaWittExponentialMultiplication
open InitialThetaWittEigenRadiusDynamics InitialThetaWittExponentialFrobenius
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem quotient_exp_sub_one (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) (k : ℕ) :
    InitialThetaWittRhoLogarithm.quotient D w ρ (exp D w ρ x - 1) k =
      InitialThetaWittExponentialLinearization.quotient D w ρ x k := by
  have he : 1 + (exp D w ρ x - 1) = exp D w ρ x := by ring
  have hp : exp D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x) =
        exp D w ρ x ^ (Arithmetic.residueChar w.1 ^ k) := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact exp_nsmul D w ρ x hx _
  rw [InitialThetaWittRhoLogarithm.quotient, he,
    InitialThetaWittExponentialLinearization.quotient, hp]

theorem log_exp (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    InitialThetaWittRhoLogarithm.logOneAdd D w ρ (exp D w ρ x - 1) = x := by
  have h := InitialThetaWittRhoLogarithm.tendsto_quotient D w ρ (exp D w ρ x - 1)
    (norm_exp_sub_one_lt_one D w ρ x hx)
  have he : InitialThetaWittRhoLogarithm.quotient D w ρ (exp D w ρ x - 1) =
      InitialThetaWittExponentialLinearization.quotient D w ρ x :=
    funext (quotient_exp_sub_one D w ρ x hx)
  rw [he] at h
  exact tendsto_nhds_unique h (InitialThetaWittExponentialLinearization.tendsto_quotient D w ρ x hx)

theorem exp_eq_exp_iff (ρ : Radius) (x y : Ring D w ρ)
    (hx : ‖x‖ < ρ.val.toReal) (hy : ‖y‖ < ρ.val.toReal) :
    exp D w ρ x = exp D w ρ y ↔ x = y := by
  constructor
  · intro h
    rw [← log_exp D w ρ x hx, h, log_exp D w ρ y hy]
  · exact congrArg (exp D w ρ)

theorem exp_eq_one_iff (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    exp D w ρ x = 1 ↔ x = 0 := by
  rw [← exp_zero D w ρ]
  exact exp_eq_exp_iff D w ρ x 0 hx (by simpa only [norm_zero] using radius_toReal_pos ρ)

theorem eigen_log_exp (ρ : Radius) (z : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val < ρ.val.toReal ^ 2) :
    InitialThetaWittRhoLogarithm.logOneAdd D w ρ
        (exp D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ z.val) - 1) =
      InitialThetaWittAllRadiusCompletion.evaluate D w ρ z.val :=
  log_exp D w ρ _ (eigen_norm_lt D w ρ z hz)

theorem eigen_exp_eq_iff (ρ : Radius) (z t : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val < ρ.val.toReal ^ 2)
    (ht : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ t.val < ρ.val.toReal ^ 2) :
    exp D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ z.val) =
      exp D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ t.val) ↔ z = t := by
  constructor
  · intro h
    apply Subtype.ext
    apply InitialThetaWittRadiusFaithfulness.evaluate_injective D w ρ
    exact (exp_eq_exp_iff D w ρ _ _ (eigen_norm_lt D w ρ z hz) (eigen_norm_lt D w ρ t ht)).mp h
  · intro h
    rw [h]

end
end JoshiTeich.Act1Scene1.InitialThetaWittLogExpInverse
