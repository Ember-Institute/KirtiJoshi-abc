import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootIntegralThreshold

/-!
source-id: JT-SCENE1-ACTUAL-FINITE-POWER-INTEGRAL-LIFT
source: original p*-divided principal Kummer class, the actual q-root and
the base Tate q-order threshold; Joshi III 3199--3236.
fidelity: constructs original saturated H1 classes of the units
1+pStar*qroot^j in the same local completion. The j=1 class is the
existing normalized class. The original integral coefficient map lifts
each finite-family class under its explicit base q-order bound.
boundary: Scene1/Derived; no identification with changing untilts or
paper theta classes is assumed, and the base bound is not automatic.
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance finitePowerPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance finitePowerCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance finitePowerAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance finitePowerContinuousSMul (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

theorem qroot_power_norm_le_one
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ j‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (iutInitialThetaFullQRoot_norm_lt_one D s).le

def finitePowerUnit
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    LocalPadicLog.principalUnits (k := localField D s) :=
  ⟨Units.mk0 (LocalPadicLog.paperPrincipalUnit (Arithmetic.residueChar s.1)
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ j))
      (LocalPadicLog.paperPrincipalUnit_ne_zero (Arithmetic.residueChar_prime s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (qroot_power_norm_le_one D s j)),
    LocalPadicLog.paperPrincipalUnit_norm_sub_one_lt_one (Arithmetic.residueChar_prime s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (qroot_power_norm_le_one D s j)⟩

def finitePowerClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    LocalPadicLog.saturatedKummerPadicSubmodule (k := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1) :=
  LocalPadicLog.paperPrincipalSaturatedClass (Ω := closure D s) (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (Additive.ofMul (finitePowerUnit D s j))

theorem finitePowerClass_log
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (finitePowerClass D s j) =
      LocalPadicLog.paperNormalizedLog (Arithmetic.residueChar s.1)
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ j) :=
  LocalPadicLog.saturatedPadicLog_paperPrincipalClass _ _ _

set_option maxHeartbeats 1000000 in
theorem finitePowerClass_one
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    finitePowerClass D s 1 = normalizedPadicClass D s := by
  apply (LocalPadicLog.saturatedPadicLogEquiv (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)).injective
  change LocalPadicLog.saturatedPadicLog _ _ _ = _
  rw [finitePowerClass_log]
  simp only [pow_one]
  change PaperLogWitnessHull.value D s =
    LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (normalizedSaturatedClass D s)
  exact (normalizedSaturatedClass_saturatedImageLog_eq_value D s).symm

theorem finitePowerClass_integralLift_iff
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    (∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x =
      (finitePowerClass D s j : continuousCohomology 1
        (LocalKummer.Rational.topRep (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1)))) ↔
      LocalPadicLog.paperNormalizedLog (Arithmetic.residueChar s.1)
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ j) ∈
        LocalPadicLog.principalLogImage (Arithmetic.residueChar s.1)
          (InitialThetaLogWitness.norm_residueChar_lt_one s.1) := by
  rw [← finitePowerClass_log D s j]
  exact LocalPadicLog.integralLift_iff_log_mem_principalLogImage _ _ _

theorem finitePowerClass_has_integralLift_of_baseQOrder
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) (hj : 0 < j)
    (hs : baseIntegralThreshold D s ≤ j * (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s)) :
    ∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x =
      (finitePowerClass D s j : continuousCohomology 1
        (LocalKummer.Rational.topRep (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1))) := by
  apply LocalPadicLog.integralLift_of_saturatedLog_small _ _ (finitePowerClass D s j)
  rw [finitePowerClass_log, LocalPadicLog.norm_paperNormalizedLog
    (Arithmetic.residueChar_prime s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (qroot_power_norm_le_one D s j)]
  exact (qroot_power_small_iff_baseQOrder D s j hj).mpr hs

theorem finitePowerClasses_have_integralLifts
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (m : ℕ)
    (hs : baseIntegralThreshold D s ≤ (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s)) :
    ∀ j ∈ Finset.Icc 1 m, ∃ x,
      LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x =
        (finitePowerClass D s j : continuousCohomology 1
          (LocalKummer.Rational.topRep (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1))) := by
  intro j hj
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  apply finitePowerClass_has_integralLift_of_baseQOrder D s j hjpos
  exact hs.trans (by
    calc
      _ = 1 * (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s) := by rw [one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ hjpos)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
