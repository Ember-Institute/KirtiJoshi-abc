import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTateKummerLog
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootOutsideUnits

/-!
source-id: JT-SCENE1-INITIAL-THETA-QROOT-TATE-LOG
source: the generic Tate-direction logarithm and the actual contracting q-root;
Joshi III 3150--3156, 3190--3236.
fidelity: packages the actual q-root only after its non-unit certificate has
been proved.  The result is a branch on ambient rational H1, not a BK claim.
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

local instance qrootLogPrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance qrootLogCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

local instance qrootLogAlgebra
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl

local instance qrootLogContinuousSMul
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

abbrev qrootClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    continuousCohomology 1 (LocalKummer.Rational.topRep
      (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1)) :=
  qrootRationalKummerClass D s

def qrootTateLog
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (continuousCohomology 1 (LocalKummer.Rational.topRep
      (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1))) →ₗ[
        ℚ_[Arithmetic.residueChar s.1]] localField D s :=
  LocalCompletion.KummerValuation.tateLog s.1 (Arithmetic.residueChar s.1) rfl
    (qrootClass D s) (qrootRationalKummerClass_not_mem_unitsSubspace D s)

set_option maxHeartbeats 1000000 in
theorem qrootTateLog_qroot
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootTateLog D s (qrootClass D s) = 0 := by
  exact LocalCompletion.KummerValuation.tateLog_q s.1
    (Arithmetic.residueChar s.1) rfl (qrootClass D s)
      (qrootRationalKummerClass_not_mem_unitsSubspace D s)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
