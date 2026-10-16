import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAmbientKummerLog
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootKummerValuation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaNormalizedClassAmbientSplit

/-!
source-id: JT-SCENE1-INITIAL-THETA-AMBIENT-KUMMER-LOG
source: actual q-root valuation correction and normalized principal-unit
Kummer class; Joshi III 3190--3236.
fidelity: evaluates the log(p)=0 branch on both original ambient H1 classes.
The normalized class maps to the existing ordinary-log witness, while the
q-root maps to its corrected-unit logarithm divided by ramification index.
These formulas do not identify the two classes or assert a BK comparison.
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
local instance ambientPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance ambientCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance ambientAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance ambientContinuousSMul
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

theorem ambientLog_normalizedRationalClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalCompletion.KummerValuation.ambientLog s.1 (Arithmetic.residueChar s.1) rfl
      (normalizedRationalClass D s) = PaperLogWitnessHull.value D s := by
  rw [LocalCompletion.KummerValuation.ambientLog_unit s.1
    (Arithmetic.residueChar s.1) rfl
    ⟨normalizedRationalClass D s, normalizedRationalClass_mem_unitsSubspace D s⟩]
  exact normalizedSaturatedClass_saturatedImageLog_eq_value D s

theorem ambientLog_qrootRationalKummerClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalCompletion.KummerValuation.ambientLog s.1 (Arithmetic.residueChar s.1) rfl
      (qrootRationalKummerClass D s) =
      (Arithmetic.ramIdx s.1 : ℚ_[Arithmetic.residueChar s.1])⁻¹ •
        LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
          (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
          ⟨LocalCompletion.KummerValuation.kummer s.1 (Arithmetic.residueChar s.1)
            (Ω := closure D s) (LocalCompletion.KummerValuation.correctedUnit s.1
              (Arithmetic.residueChar s.1) (qrootFieldUnit D s)),
            qroot_correction_mem_unitSubspace D s⟩ := by
  exact LocalCompletion.KummerValuation.ambientLog_kummer s.1
    (Arithmetic.residueChar s.1) rfl (qrootFieldUnit D s)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
