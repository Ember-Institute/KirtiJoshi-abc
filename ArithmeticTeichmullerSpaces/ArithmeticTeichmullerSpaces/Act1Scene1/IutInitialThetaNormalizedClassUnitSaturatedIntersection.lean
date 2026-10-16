import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaNormalizedClassUnitWitness
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSaturatedKummerLog

/-!
source-id: JT-SCENE1-INITIAL-THETA-NORMALIZED-CLASS-UNIT-SATURATED-INTERSECTION
source: the actual normalized rational class, ambient unit-subspace membership,
and saturated principal-unit Kummer membership (Joshi III 3190--3236).
fidelity: packages the same nonzero class in the intersection of the existing
ambient completion unit subspace and saturated principal-Kummer submodule.
This does not identify either carrier with H¹ₑ or Bloch--Kato.
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

local instance normalizedIntersectionPrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance normalizedIntersectionCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def normalizedUnitSaturatedWitness
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    {x : continuousCohomology 1 (LocalKummer.Rational.topRep
        (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1)) //
      x ∈ LocalCompletion.KummerValuation.unitsSubspace s.1
        (Arithmetic.residueChar s.1) (rfl) (Ω := closure D s) ∧
      x ∈ LocalPadicLog.saturatedKummerPadicSubmodule (k := localField D s)
        (Ω := closure D s) (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)} :=
  ⟨normalizedRationalClass D s, normalizedRationalClass_mem_unitsSubspace D s,
    (normalizedSaturatedClass D s).2⟩

theorem normalizedUnitSaturatedWitness_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (normalizedUnitSaturatedWitness D s).1 ≠ 0 := by
  simpa [normalizedUnitSaturatedWitness] using normalizedRationalClass_ne_zero D s

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
