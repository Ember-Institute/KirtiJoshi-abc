import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerImageLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPrincipalUnitLogLaws

/-!
source-id: JT-SCENE1-INITIAL-THETA-KUMMER-IMAGE-LOGARITHM
source: actual principal unit, standard rational Kummer class and ordinary
p*-normalized logarithm, Joshi III (3190--3236).
fidelity: places the actual rational class in the principal-unit Kummer image
and evaluates the image logarithm as p* times the actual log witness. It does
not identify the image with H^1_e or this logarithm with the BK logarithm.
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
local instance imageLogPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance imageLogCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def actualPrincipalUnit (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.principalUnits (k := localField D s) :=
  ⟨Units.mk0 (PaperLogWitnessHull.principalUnit D s) (principalUnit_ne_zero D s),
    PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s⟩

def rationalImageClass (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.principalKummerImage (k := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) :=
  ⟨rationalClass D s, Additive.ofMul (actualPrincipalUnit D s), rfl⟩

theorem principalImageLog_rationalImageClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.principalImageLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (rationalImageClass D s) =
        (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s) *
          PaperLogWitnessHull.value D s := by
  have he : rationalImageClass D s =
      (LocalPadicLog.principalKummerHom (k := localField D s) (Ω := closure D s)
        (Arithmetic.residueChar s.1)).rangeRestrict
          (Additive.ofMul (actualPrincipalUnit D s)) := by
    apply Subtype.ext
    rfl
  rw [he, LocalPadicLog.principalImageLog_class]
  exact log_principalUnit_eq_scale_value D s

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
