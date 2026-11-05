import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittLocalization

/-!
source-id: JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-FROBENIUS-NATIVE-INVERSE
source: Joshi II `se:ff-rings`, inverse Frobenius on the bounded Witt ring.
fidelity: exposes the inverse function of the original actual Frobenius
equivalence on the original bounded carrier, with its pointwise identity
and right-inverse law. No comparison law, norm or new source assumption
is supplied. Original proof; no reference implementation copied.
boundary: actual-side function identity only; comparison and paper
period-ring identities require separate consumers.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittLocalization.NativeFunction

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def inverseFrobeniusFun (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaBoundedWittLocalization.Ring D w :=
  (InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x

theorem inverseFrobeniusFun_eq (x : InitialThetaBoundedWittLocalization.Ring D w) :
    inverseFrobeniusFun D w x =
      (InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x := rfl

theorem inverseFrobeniusFun_rightInverse
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaBoundedWittLocalization.frobeniusEquiv D w
      (inverseFrobeniusFun D w x) = x :=
  (InitialThetaBoundedWittLocalization.frobeniusEquiv D w).apply_symm_apply x

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittLocalization.NativeFunction
