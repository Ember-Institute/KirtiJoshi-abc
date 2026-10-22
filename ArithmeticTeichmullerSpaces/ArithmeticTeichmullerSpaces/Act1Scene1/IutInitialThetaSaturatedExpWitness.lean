import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedLogEquivalence
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSaturatedKummerLog

/-!
source-id: JT-SCENE1-ACTUAL-SATURATED-EXP-WITNESS
source: actual normalized rational Kummer class and ordinary witness;
Joshi III 3226 and the proved saturated ordinary-log equivalence.
fidelity: the inverse ordinary logarithm recovers the existing actual
normalizedSaturatedClass from PaperLogWitnessHull.value. No H1e/BK or
paper theta-volume identification is inferred from this equality.
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
local instance expWitnessPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance expWitnessCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem saturatedExp_value_eq_normalizedSaturatedClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedExp (Ω := closure D s) (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (PaperLogWitnessHull.value D s) =
      normalizedSaturatedClass D s := by
  have h := congrArg
    (LocalPadicLog.saturatedExp (k := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1))
    (normalizedSaturatedClass_saturatedImageLog_eq_value D s)
  exact h.symm.trans
    (LocalPadicLog.saturatedExp_saturatedImageLog (k := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
      (normalizedSaturatedClass D s))

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
