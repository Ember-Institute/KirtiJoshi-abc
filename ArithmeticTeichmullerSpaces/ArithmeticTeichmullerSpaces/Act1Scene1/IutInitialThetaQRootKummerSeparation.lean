import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerUnitCriterion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSaturatedKummerLog

/-!
source-id: JT-SCENE1-ACTUAL-QROOT-KUMMER-SEPARATION
source: actual contracting Tate q-root and the completion Kummer unit
criterion; Joshi III 3190--3236.
fidelity: the multiplicative Kummer class of the q-root itself is nonzero
and is outside the saturated principal-unit subspace. In particular it is
different from the already constructed normalized principal-unit class.
This is an unconditional distinction on the actual full odd support.
boundary: Scene1/Derived; no H1e/BK identification is asserted.
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance separationPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance separationCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def qrootRationalKummerClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    continuousCohomology 1 (LocalKummer.Rational.topRep
      (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1)) :=
  (LocalKummer.Rational.kummerHom (Ω := closure D s) (Arithmetic.residueChar s.1)
    (Units.mk0 ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s)
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s))).toAdd

theorem qrootRationalKummerClass_not_mem_saturated
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootRationalKummerClass D s ∉ LocalPadicLog.saturatedKummerImage
      (k := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1) := by
  intro h
  have hn := (LocalCompletion.rationalKummer_mem_saturated_iff_norm_eq_one s.1
    (Arithmetic.residueChar s.1) (Ω := closure D s) rfl _).mp h
  exact (iutInitialThetaFullQRoot_norm_lt_one D s).ne hn

theorem qrootRationalKummerClass_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootRationalKummerClass D s ≠ 0 := by
  intro h
  apply qrootRationalKummerClass_not_mem_saturated D s
  rw [h]
  exact (LocalPadicLog.saturatedKummerImage
    (k := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1)).zero_mem

theorem qrootRationalKummerClass_ne_normalizedRationalClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootRationalKummerClass D s ≠ normalizedRationalClass D s := by
  intro h
  apply qrootRationalKummerClass_not_mem_saturated D s
  rw [h]
  exact normalizedRationalClass_mem_saturatedImage D s

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
