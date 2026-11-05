import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ALL-RADIUS-FROBENIUS-NATIVE-FUNCTION
source: Joshi II `se:ff-rings`, continuous Frobenius on the all-radius period carrier.
fidelity: saves the original actual Carrier Frobenius as a function and
proves its pointwise/full-function identities, dense-inclusion action and
continuity. No carrier, map, norm or source assumption is changed.
Original proof; no reference implementation copied.
boundary: function interface only; actual-standard and paper identities
must be proved by separate consumers.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusFrobenius.NativeFunction

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def frobeniusFun
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    InitialThetaWittAllRadiusCompletion.Carrier D w :=
  InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x

theorem frobeniusEquiv_eq_frobeniusFun
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x =
      frobeniusFun D w x := rfl

theorem frobeniusEquiv_toFun_eq_frobeniusFun :
    (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w :
      InitialThetaWittAllRadiusCompletion.Carrier D w →
        InitialThetaWittAllRadiusCompletion.Carrier D w) =
      frobeniusFun D w := rfl

theorem frobeniusFun_inclusion
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    frobeniusFun D w (InitialThetaWittAllRadiusCompletion.inclusion D w x) =
      InitialThetaWittAllRadiusCompletion.inclusion D w
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) := by
  rw [← frobeniusEquiv_eq_frobeniusFun]
  exact InitialThetaWittAllRadiusFrobenius.frobenius_inclusion D w x

theorem frobeniusFun_continuous :
    Continuous (frobeniusFun D w) := by
  rw [← frobeniusEquiv_toFun_eq_frobeniusFun]
  exact InitialThetaWittAllRadiusFrobenius.frobenius_continuous D w

end
end JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusFrobenius.NativeFunction
