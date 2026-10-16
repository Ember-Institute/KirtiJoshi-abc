import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPrincipalUnitAmbientSplit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPrincipalUnitLogLaws

/-!
source-id: JT-SCENE1-INITIAL-THETA-NORMALIZED-CLASS-AMBIENT-SPLIT
source: the actual p*-normalized rational class, its scalar identity, and
the ambient completion Kummer unit subspace (Joshi III 3226--3236).
fidelity: transfers the already proved field-element unit-subspace membership
through the nonzero paper normalization scalar. This is an ambient H1 fact;
it does not identify the subspace with H^1_e or Bloch--Kato.
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

local instance normalizedAmbientPrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance normalizedAmbientCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem normalizedRationalClass_mem_unitsSubspace
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    normalizedRationalClass D s ∈ LocalCompletion.KummerValuation.unitsSubspace s.1
      (Arithmetic.residueChar s.1) (rfl) (Ω := closure D s) := by
  let U := LocalCompletion.KummerValuation.unitsSubspace s.1
      (Arithmetic.residueChar s.1) (rfl) (Ω := closure D s)
  let c : ℚ_[Arithmetic.residueChar s.1] :=
    LocalPadicLog.paperScale (Arithmetic.residueChar s.1)
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr
    (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1))
  have hr : rationalClass D s ∈ U :=
    rationalClass_mem_unitsSubspace D s
  have hi : c⁻¹ • rationalClass D s ∈ U := U.smul_mem c⁻¹ hr
  rw [← scale_normalizedRationalClass D s] at hi
  simpa [c, smul_smul, inv_mul_cancel₀ hc, one_smul] using hi

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
