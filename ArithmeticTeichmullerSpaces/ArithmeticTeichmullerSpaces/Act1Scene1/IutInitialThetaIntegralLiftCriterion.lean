import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCoefficientKernel
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaIntegralKummerNonTorsion

/-!
source-id: JT-SCENE1-ACTUAL-INTEGRAL-LIFT-CRITERION
source: the actual integral/rational Kummer classes and p*-normalization,
Joshi III 3214--3236; the proved full coefficient-kernel criterion.
fidelity: actual rational lifts are unique modulo p-power torsion. Lifting
the existing p*-divided rational class is equivalent to p*-divisibility of
the actual integral class modulo that torsion. Existence is not assumed.
boundary: Scene1/Derived; integral-H1 intersection and H1e/BK remain open.
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance liftPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance liftCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem integralLift_rationalClass_iff
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (x : continuousCohomology 1 (LocalKummer.padicTateTopRep
      (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1))) :
    LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x = rationalClass D s ↔
      ∃ n : ℕ, (Arithmetic.residueChar s.1 ^ n) • (x - padicClass D s) = 0 := by
  rw [rationalClass_eq_changeCoefficients]
  exact LocalKummer.Rational.standardMap_eq_iff_prime_power_difference _ _ _

theorem integralLift_normalizedClass_iff
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (x : continuousCohomology 1 (LocalKummer.padicTateTopRep
      (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1))) :
    LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x = normalizedRationalClass D s ↔
      ∃ n : ℕ, (Arithmetic.residueChar s.1 ^ n) •
        ((LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : ℤ_[Arithmetic.residueChar s.1]) •
          x - padicClass D s) = 0 := by
  have hr : (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) :
      ℤ_[Arithmetic.residueChar s.1]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1))
  have he := LocalKummer.Rational.standardMap_eq_divided_iff (Arithmetic.residueChar s.1)
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : ℤ_[Arithmetic.residueChar s.1])
    hr x (padicClass D s)
  simpa only [PadicInt.coe_natCast, ← rationalClass_eq_changeCoefficients,
    normalizedRationalClass] using he

theorem normalizedClass_has_integralLift_iff
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x = normalizedRationalClass D s) ↔
      ∃ x, ∃ n : ℕ, (Arithmetic.residueChar s.1 ^ n) •
        ((LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : ℤ_[Arithmetic.residueChar s.1]) •
          x - padicClass D s) = 0 :=
  exists_congr (integralLift_normalizedClass_iff D s)

def torsionFreePadicClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :=
  (LocalKummer.Rational.coefficientTorsion (K := localField D s) (Ω := closure D s)
    (Arithmetic.residueChar s.1)).mkQ (padicClass D s)

theorem torsionFreePadicClass_map
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalKummer.Rational.torsionFreeCoefficient (Arithmetic.residueChar s.1)
      (torsionFreePadicClass D s) = rationalClass D s :=
  (rationalClass_eq_changeCoefficients D s).symm

theorem torsionFreePadicClass_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    torsionFreePadicClass D s ≠ 0 := by
  intro h
  apply rationalClass_ne_zero D s
  rw [← torsionFreePadicClass_map D s, h, map_zero]

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
