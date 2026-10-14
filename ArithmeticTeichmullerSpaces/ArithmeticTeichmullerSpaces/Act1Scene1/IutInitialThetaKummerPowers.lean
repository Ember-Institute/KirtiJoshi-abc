import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerMultiplicativity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaMathlibKummer

/-!
source-id: JT-SCENE1-INITIAL-THETA-KUMMER-POWERS
source: Joshi III actual principal unit (3190--3208) and p*-normalization (3226).
fidelity: identifies the actual class with the unit-group Kummer homomorphism.
Powers of the actual principal unit map to scalar multiples, including p*.
This supplies integral scalar accounting, not division by p* or a BK comparison.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def principalUnitUnit (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (localField D s)ˣ :=
  Units.mk0 (PaperLogWitnessHull.principalUnit D s) (principalUnit_ne_zero D s)

theorem mathlibClass_eq_kummerHom
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    mathlibClass D s = (LocalKummer.kummerHom (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (Arithmetic.residueChar_prime s.1).pos
      (principalUnitUnit D s)).toAdd := rfl

theorem principalUnit_pow_class
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (n : ℕ) :
    (LocalKummer.kummerHom (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (Arithmetic.residueChar_prime s.1).pos
      (principalUnitUnit D s ^ n)).toAdd = n • mathlibClass D s := by
  rw [LocalKummer.kummerHom_pow, ← mathlibClass_eq_kummerHom]

theorem principalUnit_paperScale_class
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (LocalKummer.kummerHom (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (Arithmetic.residueChar_prime s.1).pos
      (principalUnitUnit D s ^ LocalPadicLog.paperScale (Arithmetic.residueChar s.1))).toAdd =
        LocalPadicLog.paperScale (Arithmetic.residueChar s.1) • mathlibClass D s :=
  principalUnit_pow_class D s _

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
