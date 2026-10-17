import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootOutsideNormalizedSpan
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootTateLogConsumers

/-!
source-id: JT-SCENE1-INITIAL-THETA-QROOT-NORMALIZED-LINEAR-INDEPENDENT
source: the actual contracting q-root and normalized principal-unit Kummer
classes; Joshi III 3190--3236.
fidelity: packages the two previously proved span-separation statements as a
finite linear-independence certificate. It does not identify either line with
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

local instance linearIndependentPrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance linearIndependentCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem qroot_normalized_linearIndependent
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LinearIndependent ℚ_[Arithmetic.residueChar s.1]
      ![normalizedRationalClass D s, qrootRationalKummerClass D s] := by
  rw [linearIndependent_fin2]
  constructor
  · exact qrootRationalKummerClass_ne_zero D s
  · intro a ha
    exact normalizedRationalClass_not_mem_qroot_span D s
      (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
