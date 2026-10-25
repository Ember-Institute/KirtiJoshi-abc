import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusPadicScalars
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoExpansion
import Mathlib.Topology.Algebra.Algebra

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PADIC-SCALAR-CONTINUITY
source: Joshi II `se:ff-rings`, the topological Q_p algebra structure
on the period ring equipped with its rho norms.
fidelity: integral prime-field Witt constants have rho norm at most
one. Factoring a small p-adic scalar by p^N bounds its image by rho^N.
Proves continuity of the existing Q_p maps into each radius completion
and the common complete ring, and joint continuity of their actual
scalar actions. No continuity or scalar norm law is an input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; exact scalar norm laws, multiplicative norm
equality, Tate-log eigenspace and paper B/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPadicScalarContinuity

open JoshiTeich.Prologue
open InitialThetaBoundedWittPadicScalars InitialThetaWittAllRadiusPadicScalars
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

instance completedNormOne (ρ : Radius) : NormOneClass (InitialThetaWittRhoCompletion.Completed D w ρ) where
  norm_one := by
    have h := InitialThetaWittRhoCompletion.inclusion_norm D w ρ 1
    rw [map_one, InitialThetaWittRhoNorm.realValue_one D w ρ.val
      ρ.property.1.ne' ρ.property.2.le] at h
    exact h

theorem norm_completedPadicInt_le_one (ρ : Radius)
    (a : PadicInt (Arithmetic.residueChar w.1)) :
    ‖completedPadicMap D w ρ (algebraMap _ (Padic (Arithmetic.residueChar w.1)) a)‖ ≤ 1 := by
  change ‖InitialThetaWittRhoCompletion.inclusion D w ρ (padicMap D w (algebraMap _ _ a))‖ ≤ 1
  rw [padicMap_algebraMap]
  exact InitialThetaWittRhoExpansion.norm_ainfMap_le_one D w ρ
    (WittVector.map
      (ZMod.castHom (dvd_refl (Arithmetic.residueChar w.1)) (InitialThetaTiltIntegers.Integers D w))
      ((WittVector.equiv (Arithmetic.residueChar w.1)).symm a))

theorem norm_completed_prime (ρ : Radius) :
    ‖(Arithmetic.residueChar w.1 : InitialThetaWittRhoCompletion.Completed D w ρ)‖ = ρ.val.toReal := by
  simpa only [map_natCast] using InitialThetaWittRhoCompletion.inclusion_prime_norm D w ρ

theorem norm_completedPadicMap_le_of_small (ρ : Radius) (N : ℕ)
    (a : Padic (Arithmetic.residueChar w.1))
    (ha : ‖a‖ ≤ ‖(Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ N‖) :
    ‖completedPadicMap D w ρ a‖ ≤ ρ.val.toReal ^ N := by
  let p := Arithmetic.residueChar w.1
  have hp0 : (p : Padic p) ≠ 0 := Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero
  have hpow : (p : Padic p) ^ N ≠ 0 := pow_ne_zero N hp0
  let b : PadicInt p := ⟨a / (p : Padic p) ^ N, by
    change ‖a / (p : Padic p) ^ N‖ ≤ 1
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hpow)).mpr ha⟩
  have hab : (p : Padic p) ^ N * algebraMap (PadicInt p) (Padic p) b = a := by
    change (p : Padic p) ^ N * (a / (p : Padic p) ^ N) = a
    exact mul_div_cancel₀ a hpow
  rw [← hab, map_mul, map_pow, map_natCast]
  calc
    _ ≤ ‖(p : InitialThetaWittRhoCompletion.Completed D w ρ) ^ N‖ *
        ‖completedPadicMap D w ρ (algebraMap (PadicInt p) (Padic p) b)‖ := norm_mul_le _ _
    _ ≤ ‖(p : InitialThetaWittRhoCompletion.Completed D w ρ)‖ ^ N * 1 :=
      mul_le_mul (norm_pow_le _ _) (norm_completedPadicInt_le_one D w ρ b)
        (norm_nonneg _) (pow_nonneg (norm_nonneg _) N)
    _ = _ := by rw [norm_completed_prime, mul_one]

theorem completedPadicMap_continuous (ρ : Radius) : Continuous (completedPadicMap D w ρ) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hr : ρ.val.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
        ρ.property.2
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr
  have hp0 : (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero
  filter_upwards [eventually_norm_sub_lt a (norm_pos_iff.mpr (pow_ne_zero N hp0))] with x hx
  rw [dist_eq_norm, ← map_sub]
  exact (norm_completedPadicMap_le_of_small D w ρ N (x - a) hx.le).trans_lt hN

instance completedContinuousSMul (ρ : Radius) :
    ContinuousSMul (Padic (Arithmetic.residueChar w.1)) (InitialThetaWittRhoCompletion.Completed D w ρ) :=
  continuousSMul_of_algebraMap _ _ (completedPadicMap_continuous D w ρ)

theorem commonPadicMap_continuous : Continuous (commonPadicMap D w) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w _ _ _).mpr
  intro ρ
  exact (completedPadicMap_continuous D w ρ).tendsto a

instance commonContinuousSMul : ContinuousSMul (Padic (Arithmetic.residueChar w.1)) (Carrier D w) :=
  continuousSMul_of_algebraMap _ _ (commonPadicMap_continuous D w)

theorem coordinateSeminorm_smul_le (ρ : Radius)
    (a : Padic (Arithmetic.residueChar w.1)) (x : Carrier D w) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (a • x) ≤
      ‖completedPadicMap D w ρ a‖ *
        InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x := by
  change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (a • x)‖ ≤
    ‖completedPadicMap D w ρ a‖ * ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖
  rw [evaluate_smul, Algebra.smul_def]
  exact norm_mul_le _ _

end
end JoshiTeich.Act1Scene1.InitialThetaWittPadicScalarContinuity
