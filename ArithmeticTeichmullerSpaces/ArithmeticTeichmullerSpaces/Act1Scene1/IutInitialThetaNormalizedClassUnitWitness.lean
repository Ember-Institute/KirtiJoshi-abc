import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaNormalizedClassAmbientSplit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRationalKummerNonzero

/-!
source-id: JT-SCENE1-INITIAL-THETA-NORMALIZED-CLASS-UNIT-WITNESS
source: the actual normalized rational class, its ambient unit-subspace
membership, and its previously proved nonvanishing (Joshi III 3190--3236).
fidelity: packages the class as a nonzero element of the existing ambient
completion Kummer unit subspace. This does not identify the subspace with
H¹ₑ or Bloch--Kato.
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

local instance normalizedWitnessPrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance normalizedWitnessCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def normalizedUnitWitness
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalCompletion.KummerValuation.unitsSubspace s.1
      (Arithmetic.residueChar s.1) (rfl) (Ω := closure D s) :=
  ⟨normalizedRationalClass D s, normalizedRationalClass_mem_unitsSubspace D s⟩

theorem normalizedUnitWitness_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    normalizedUnitWitness D s ≠ 0 := by
  intro h
  apply normalizedRationalClass_ne_zero D s
  have hv := congrArg Subtype.val h
  simpa [normalizedUnitWitness] using hv

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
