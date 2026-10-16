import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerIntegralIntersection
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSaturatedKummerLog

/-!
source-id: JT-SCENE1-ACTUAL-INTEGRAL-ROOT-CRITERION
source: actual p*-normalized rational class, Joshi III 3199--3236,
and finite-level Kummer root descent. No reference code is copied.
fidelity: integral lifting of the existing normalized class is equivalent
to a concrete equation in its actual local completion, with p*=p^m.
Existence of a solution, H1e/BK and paper volume identities are not assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance rootLiftPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance rootLiftCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem normalizedClass_integralLift_iff_power_root
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x = normalizedRationalClass D s) ↔
      ∃ n : ℕ, ∃ b : localField D s,
        b ^ (Arithmetic.residueChar s.1 ^ ((if Arithmetic.residueChar s.1 = 2 then 2 else 1) + n)) =
          PaperLogWitnessHull.principalUnit D s ^ (Arithmetic.residueChar s.1 ^ n) := by
  have hscale : (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) :
      ℚ_[Arithmetic.residueChar s.1]) =
        (Arithmetic.residueChar s.1 : ℚ_[Arithmetic.residueChar s.1]) ^
          (if Arithmetic.residueChar s.1 = 2 then 2 else 1) := by
    rw [LocalPadicLog.paperScale_eq_prime_pow, Nat.cast_pow]
  have hclass : (LocalKummer.Rational.kummerHom (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (actualPrincipalUnit D s).1).toAdd = rationalClass D s := rfl
  have ha : ((actualPrincipalUnit D s).1 : localField D s) =
      PaperLogWitnessHull.principalUnit D s := rfl
  have h := LocalKummer.Rational.exists_integralLift_dividedKummer_iff
    (Ω := closure D s) (Arithmetic.residueChar s.1) (actualPrincipalUnit D s).1
      (if Arithmetic.residueChar s.1 = 2 then 2 else 1)
  simpa only [hclass, ha, ← hscale, normalizedRationalClass] using h

set_option maxHeartbeats 1000000 in
theorem normalizedClass_integralLift_iff_principalImage
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x = normalizedRationalClass D s) ↔
      normalizedRationalClass D s ∈ LocalPadicLog.principalKummerImage
        (k := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1) :=
  LocalPadicLog.integralLift_iff_mem_principalImage (k := localField D s) (Ω := closure D s)
    (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (normalizedSaturatedClass D s)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
