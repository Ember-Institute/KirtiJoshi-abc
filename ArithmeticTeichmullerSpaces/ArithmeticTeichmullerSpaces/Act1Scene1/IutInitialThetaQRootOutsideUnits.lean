import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerCoordinates
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootKummerSeparation

/-!
source-id: JT-SCENE1-INITIAL-THETA-QROOT-OUTSIDE-UNITS
source: the actual contracting q-root and the completion unit criterion;
Joshi III 3190--3236.
fidelity: isolates the one non-unit certificate needed by the Tate-log
consumer.  It does not construct a new H1 class or identify a BK subspace.
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

local instance outsidePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance outsideCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem qrootRationalKummerClass_not_mem_unitsSubspace
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootRationalKummerClass D s ∉
      LocalCompletion.KummerValuation.unitsSubspace s.1
        (Arithmetic.residueChar s.1) rfl (Ω := closure D s) := by
  intro h
  apply qrootRationalKummerClass_not_mem_saturated D s
  exact h

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
