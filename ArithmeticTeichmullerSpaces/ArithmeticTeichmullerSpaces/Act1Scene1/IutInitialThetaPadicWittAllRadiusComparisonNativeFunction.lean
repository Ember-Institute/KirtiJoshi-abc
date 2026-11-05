import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittAllRadiusComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-ALL-RADIUS-COMPARISON-NATIVE-FUNCTION
source: Joshi II `se:ff-rings`, comparison of all-radius completions.
fidelity: exposes the existing actual-standard Carrier ring equivalence
as its original function, with continuity and the proved inclusion-value
formula. Its implementation and identity are explicit; no comparison law,
carrier, norm or additional source assumption is introduced.
Original proof; no reference implementation copied.
boundary: function interface only; Frobenius and paper identities remain
separate consumers.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittAllRadiusComparison.NativeFunction

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeComparisonNativeFunction :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def ringEquivFun
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1) :=
  InitialThetaPadicWittAllRadiusComparison.ringEquiv D w x

theorem ringEquiv_eq_ringEquivFun
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    InitialThetaPadicWittAllRadiusComparison.ringEquiv D w x =
      ringEquivFun D w x := by
  rfl

theorem ringEquivFun_continuous :
    Continuous (ringEquivFun D w) := by
  have hfun :
      (InitialThetaPadicWittAllRadiusComparison.ringEquiv D w :
        InitialThetaWittAllRadiusCompletion.Carrier D w →
          PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1)) =
        ringEquivFun D w :=
    funext (ringEquiv_eq_ringEquivFun D w)
  rw [← hfun]
  exact InitialThetaPadicWittAllRadiusComparison.ringEquiv_continuous D w

theorem ringEquivFun_inclusion_val
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (ringEquivFun D w
      (InitialThetaWittAllRadiusCompletion.inclusion D w x)).val =
      PadicWittAllRadiusCompletion.diagonalFun (Arithmetic.residueChar w.1)
        (InitialThetaPadicBoundedWittComparison.ringFun D w x) := by
  simpa only [ringEquivFun] using
    InitialThetaPadicWittAllRadiusComparison.ringEquiv_inclusion_val D w x

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittAllRadiusComparison.NativeFunction
