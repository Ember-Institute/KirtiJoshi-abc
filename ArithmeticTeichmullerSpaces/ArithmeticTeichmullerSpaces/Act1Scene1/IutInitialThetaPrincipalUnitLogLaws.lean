import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogHomomorphism
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCoefficientChange

/-!
source-id: JT-SCENE1-INITIAL-THETA-PRINCIPAL-UNIT-LOG-LAWS
source: Joshi III principal unit (3190), p*-normalized logarithm (3226).
fidelity: proves the actual principal-unit logarithm power and inverse laws,
its nonvanishing and infinite multiplicative order. It constructs division
of the actual rational Kummer class by p*, with a scalar cancellation law.
The ordinary logarithm and this class are not identified by a BK theorem.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance principalLogResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance principalLogCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem log_principalUnit_eq_scale_value
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.padicLog (PaperLogWitnessHull.principalUnit D s) =
      (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s) *
        PaperLogWitnessHull.value D s := by
  rw [PaperLogWitnessHull.value_eq_log_principalUnit, mul_inv_cancel_left₀]
  exact Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1))

theorem log_principalUnit_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.padicLog (PaperLogWitnessHull.principalUnit D s) ≠ 0 := by
  rw [log_principalUnit_eq_scale_value]
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1)))
    (PaperLogWitnessHull.value_ne_zero D s)

theorem log_principalUnit_pow
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (n : ℕ) :
    LocalPadicLog.padicLog (PaperLogWitnessHull.principalUnit D s ^ n) =
      (n : localField D s) * LocalPadicLog.padicLog (PaperLogWitnessHull.principalUnit D s) :=
  LocalPadicLog.padicLog_pow (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s) n

theorem normalized_log_principalUnit_pow
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (n : ℕ) :
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s)⁻¹ *
      LocalPadicLog.padicLog (PaperLogWitnessHull.principalUnit D s ^ n) =
        (n : localField D s) * PaperLogWitnessHull.value D s := by
  rw [log_principalUnit_pow, PaperLogWitnessHull.value_eq_log_principalUnit]
  ring

theorem log_principalUnit_inv
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.padicLog (PaperLogWitnessHull.principalUnit D s)⁻¹ =
      -LocalPadicLog.padicLog (PaperLogWitnessHull.principalUnit D s) :=
  LocalPadicLog.padicLog_inv (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s)

theorem principalUnit_pow_ne_one
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (n : ℕ) (hn : n ≠ 0) : PaperLogWitnessHull.principalUnit D s ^ n ≠ 1 := by
  intro h
  exact log_principalUnit_ne_zero D s
    (LocalPadicLog.padicLog_eq_zero_of_pow_eq_one (Arithmetic.residueChar_prime s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
      (PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s) hn h)

def normalizedRationalClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    continuousCohomology 1 (LocalKummer.Rational.topRep (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1)) :=
  (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : ℚ_[Arithmetic.residueChar s.1])⁻¹ •
    rationalClass D s

theorem scale_normalizedRationalClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : ℚ_[Arithmetic.residueChar s.1]) •
      normalizedRationalClass D s = rationalClass D s := by
  unfold normalizedRationalClass
  rw [smul_smul, mul_inv_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1))

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
