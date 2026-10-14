import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicRationalKummerNonvanishing
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaIntegralKummerNonzero

/-!
source-id: JT-SCENE1-INITIAL-THETA-RATIONAL-KUMMER-NONZERO
source: actual principal-unit rational Kummer class, Joshi III (3190--3236).
fidelity: the actual standard rational class and its p*-normalized scalar
multiple are nonzero. This rules out a rational coboundary for this class;
it does not prove coefficient injectivity for all classes or H^1_e/BK identity.
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

local instance rationalNonzeroResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance rationalNonzeroCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem rationalClass_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : rationalClass D s ≠ 0 :=
  LocalPadicLog.rationalKummer_ne_zero_of_log_ne_zero (rootTower D s)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s) (log_principalUnit_ne_zero D s)

theorem normalizedRationalClass_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : normalizedRationalClass D s ≠ 0 := by
  intro h
  apply rationalClass_ne_zero D s
  rw [← scale_normalizedRationalClass D s, h, smul_zero]

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
