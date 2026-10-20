import ArithmeticTeichmullerSpaces.Act1Scene1.AdicLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamTeichmuller
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCyclotomicTateTilt

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-LOGARITHM
source: Joshi II multiplicative-formal-group Tate period (935--958),
local period rings (1069--1076), and Mathlib formal-log evaluation.
fidelity: derives rational scalars and a linear topology on the original
complete B_dR+; evaluates the convergent logarithm at its actual theta-kernel
elements, with exact kernel, norm and nonvanishing laws. Applies this to
the original Tate tower's [epsilon]-1 through the original Ainf map.
Injectivity of that Ainf-to-completion map, additive Tate-period and
Frobenius-p identities, Frechet B/rho norms and BK remain separate obligations.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamLogarithm

open JoshiTeich.Prologue InitialThetaDeRhamCompletion InitialThetaDeRhamField
open InitialThetaDeRhamTopology
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

/-- All nonzero integers are units, as their original theta images are nonzero. -/
theorem intCast_isUnit (z : ℤ) (hz : z ≠ 0) : IsUnit (z : Ring D w) := by
  apply (isUnit_iff D w _).mpr
  rw [map_intCast]
  exact Int.cast_ne_zero.mpr hz

def rationalMap : ℚ →+* Ring D w :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ)
    (g := Int.castRingHom (Ring D w)) (fun z =>
      intCast_isUnit D w z.1 (mem_nonZeroDivisors_iff_ne_zero.mp z.2))

instance rationalAlgebra : Algebra ℚ (Ring D w) := (rationalMap D w).toAlgebra

instance linearTopology : IsLinearTopology (Ring D w) (Ring D w) :=
  IsLinearTopology.mk_of_hasBasis _ (plus_isAdic D w).hasBasis_nhds_zero

theorem hasEval_kernel (a : Ring D w) (ha : theta D w a = 0) : PowerSeries.HasEval a := by
  change Filter.Tendsto (fun n : ℕ => a ^ n) Filter.atTop (𝓝 0)
  apply (plus_isAdic D w).hasBasis_nhds_zero.tendsto_right_iff.mpr
  intro n _
  refine Filter.eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
  exact Ideal.pow_le_pow_right hm ((RingHom.ker (theta D w)).pow_mem_pow ha m)

/-- The original B_dR+ value of the convergent log(1+a). -/
def logOneAdd (a : Ring D w) (ha : theta D w a = 0) : Ring D w :=
  AdicLogarithm.oneAdd (Ring D w) a (hasEval_kernel D w a ha)

theorem hasSum_logOneAdd (a : Ring D w) (ha : theta D w a = 0) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.log (Ring D w)) * a ^ n)
      (logOneAdd D w a ha) :=
  AdicLogarithm.hasSum_oneAdd (Ring D w) a (hasEval_kernel D w a ha)

theorem logOneAdd_eq_mul_unit (a : Ring D w) (ha : theta D w a = 0) :
    ∃ u : (Ring D w)ˣ, logOneAdd D w a ha = a * u :=
  AdicLogarithm.oneAdd_eq_mul_unit (Ring D w) a (hasEval_kernel D w a ha)

theorem theta_logOneAdd (a : Ring D w) (ha : theta D w a = 0) :
    theta D w (logOneAdd D w a ha) = 0 :=
  AdicLogarithm.oneAdd_mem_ideal (Ring D w) (RingHom.ker (theta D w)) a
    (hasEval_kernel D w a ha) ha

theorem logOneAdd_eq_zero_iff (a : Ring D w) (ha : theta D w a = 0) :
    logOneAdd D w a ha = 0 ↔ a = 0 :=
  AdicLogarithm.oneAdd_eq_zero_iff (Ring D w) a (hasEval_kernel D w a ha)

theorem norm_unit (u : (Ring D w)ˣ) : ‖(u : Ring D w)‖ = 1 := by
  rw [← inclusion_norm D w, norm_eq_value,
    (InitialThetaDeRhamValuation.valuation_eq_one_iff_theta_ne_zero D w u).mpr
      ((isUnit_iff D w u).mp u.isUnit), map_one]
  rfl

/-- This is the existing primitive-adic norm, with no untilt-norm identification. -/
theorem norm_logOneAdd (a : Ring D w) (ha : theta D w a = 0) :
    ‖logOneAdd D w a ha‖ = ‖a‖ := by
  obtain ⟨u, hu⟩ := logOneAdd_eq_mul_unit D w a ha
  rw [hu, ← inclusion_norm D w, map_mul, norm_mul,
    inclusion_norm, inclusion_norm, norm_unit, mul_one]

/-- The original Tate kernel coordinate mapped through the existing Ainf-to-plus hom. -/
def tateCoordinate (x : InitialThetaCyclotomicTateTilt.Tate D w) : Ring D w :=
  InitialThetaDeRhamTeichmuller.ainfToPlus D w
    (InitialThetaCyclotomicTateTilt.kernelCoordinate D w x)

theorem theta_tateCoordinate (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    theta D w (tateCoordinate D w x) = 0 := by
  rw [tateCoordinate, InitialThetaDeRhamTeichmuller.theta_ainfToPlus]
  exact congrArg (fun z : LocalGeometricFontaine.integerRing
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) =>
      (z : InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (InitialThetaCyclotomicTateTilt.kernelCoordinate_mem_ker D w x)

def tateLog (x : InitialThetaCyclotomicTateTilt.Tate D w) : Ring D w :=
  logOneAdd D w (tateCoordinate D w x) (theta_tateCoordinate D w x)

theorem hasSum_tateLog (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.log (Ring D w)) *
      tateCoordinate D w x ^ n) (tateLog D w x) :=
  hasSum_logOneAdd D w _ _

theorem theta_tateLog (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    theta D w (tateLog D w x) = 0 := theta_logOneAdd D w _ _

theorem norm_tateLog (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    ‖tateLog D w x‖ = ‖tateCoordinate D w x‖ := norm_logOneAdd D w _ _

theorem tateLog_eq_zero_iff (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    tateLog D w x = 0 ↔ tateCoordinate D w x = 0 := logOneAdd_eq_zero_iff D w _ _

end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamLogarithm
