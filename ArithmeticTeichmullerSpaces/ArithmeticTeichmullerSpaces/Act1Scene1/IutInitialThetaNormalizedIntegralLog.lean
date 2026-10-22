import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerNormalizedIntegralLog
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePowerIntegralLift

/-!
source-id: JT-SCENE1-ACTUAL-NORMALIZED-INTEGRAL-LOG
source: actual integral Kummer class and principal units 1+pStar*qroot^j;
Joshi III 3190--3236, especially the linear-power remark near 3199.
fidelity: the original actual class, and every linear-power integral
Kummer class, have normalized ordinary log equal to the paper witness
without a base q-order bound. The map is explicitly log/pStar; the old
divided rational classes and their integral-lift criteria are unchanged.
boundary: Scene1/Derived; the normalized ordinary map is not identified
with the BK logarithm or with classes in different untilts.
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance normalizedIntegralPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance normalizedIntegralCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance normalizedIntegralAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance normalizedIntegralFinite (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    FiniteDimensional ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.finite_padicAlgebra (w := s.1) rfl
local instance normalizedIntegralContinuousSMul (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

def actualIntegralImageClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.integralKummerSubmodule (Ω := closure D s) (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) :=
  LocalPadicLog.principalIntegralClass _ _ (Additive.ofMul (actualPrincipalUnit D s))

set_option maxHeartbeats 1000000 in
theorem actualIntegralImageClass_coefficient
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (actualIntegralImageClass D s).1.1 =
      LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) (padicClass D s) :=
  rationalClass_eq_changeCoefficients D s

theorem actualIntegralImageClass_normalizedLog
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (LocalPadicLog.normalizedIntegralKummerLogEquiv (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (actualIntegralImageClass D s) : localField D s) =
        PaperLogWitnessHull.value D s :=
  LocalPadicLog.normalizedIntegralKummerLog_principal (k := localField D s) (Ω := closure D s)
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (Additive.ofMul (actualPrincipalUnit D s))

def finitePowerIntegralImageClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    LocalPadicLog.integralKummerSubmodule (Ω := closure D s) (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) :=
  LocalPadicLog.principalIntegralClass _ _ (Additive.ofMul (finitePowerUnit D s j))

theorem finitePowerIntegralImageClass_normalizedLog
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    (LocalPadicLog.normalizedIntegralKummerLogEquiv (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (finitePowerIntegralImageClass D s j) : localField D s) =
        LocalPadicLog.paperNormalizedLog (Arithmetic.residueChar s.1)
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ j) :=
  LocalPadicLog.normalizedIntegralKummerLog_principal (k := localField D s) (Ω := closure D s)
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (Additive.ofMul (finitePowerUnit D s j))

theorem finitePowerIntegralImageClass_has_integralLift
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    ∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x =
      (finitePowerIntegralImageClass D s j).1.1 :=
  (LocalPadicLog.mem_integralKummerSubmodule_iff _ _ _).mp (finitePowerIntegralImageClass D s j).2

set_option maxHeartbeats 1000000 in
theorem finitePowerIntegralImageClass_divided_eq
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (j : ℕ) :
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : ℚ_[Arithmetic.residueChar s.1])⁻¹ •
      (finitePowerIntegralImageClass D s j).1 = finitePowerClass D s j := rfl

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
