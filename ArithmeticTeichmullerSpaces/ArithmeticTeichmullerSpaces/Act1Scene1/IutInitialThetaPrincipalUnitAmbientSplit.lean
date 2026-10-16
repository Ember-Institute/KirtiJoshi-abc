import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerSpan
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRationalKummer

/-!
source-id: JT-SCENE1-INITIAL-THETA-PRINCIPAL-UNIT-AMBIENT-SPLIT
source: actual principal-unit Kummer class and the completion norm-one
criterion (Joshi III 3190--3236).
fidelity: identifies the actual principal-unit rational class with the
existing field-element Kummer homomorphism and places it in the already
constructed ambient unit subspace. This does not identify that subspace
with H^1_e or a Bloch--Kato space.
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

local instance ambientSplitPrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance ambientSplitCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem rationalClass_eq_fieldKummer
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    rationalClass D s =
      (LocalKummer.Rational.kummerHom (K := localField D s) (Ω := closure D s)
        (Arithmetic.residueChar s.1)
        (Units.mk0 (PaperLogWitnessHull.principalUnit D s)
          (principalUnit_ne_zero D s))).toAdd := by
  let R := LocalKummer.rootTower (Ω := closure D s)
    (Arithmetic.residueChar s.1) (Arithmetic.residueChar_prime s.1).pos
    (PaperLogWitnessHull.principalUnit D s)
  rw [rationalClass_eq_representative D s]
  change LocalKummer.Rational.classOfCocycle (Arithmetic.residueChar s.1)
      (continuousCocycleValue D s) = _
  rw [← LocalKummer.Rational.toH1_class]
  exact congrArg (LocalKummer.Rational.toH1 (Arithmetic.residueChar s.1))
    (kummerClass_eq_of_rootTower D s R)

theorem rationalClass_mem_unitsSubspace
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    rationalClass D s ∈ LocalCompletion.KummerValuation.unitsSubspace s.1
      (Arithmetic.residueChar s.1) (rfl) (Ω := closure D s) := by
  rw [rationalClass_eq_fieldKummer D s]
  apply (LocalCompletion.rationalKummer_mem_saturated_iff_norm_eq_one s.1
    (Arithmetic.residueChar s.1) (Ω := closure D s) rfl _).mpr
  exact LocalPadicLog.norm_eq_one_of_norm_sub_one_lt
    (PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
