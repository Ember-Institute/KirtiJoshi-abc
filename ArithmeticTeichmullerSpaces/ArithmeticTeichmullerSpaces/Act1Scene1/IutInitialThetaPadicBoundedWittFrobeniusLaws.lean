import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittFrobeniusComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-BOUNDED-WITT-FROBENIUS-LAWS
source: Joshi II `se:ff-rings`, functorial Frobenius on bounded Witt rings.
fidelity: derives the two forward bare-function forms from the proved
canonical native commutation. Original proof; original maps retained.
boundary: inverse wrappers, completion and paper identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeBoundedFrobeniusLaws :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem ringFun_frobenius_native
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ringFun D w
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) =
      PadicWittRhoFrobenius.NativeFunction.frobeniusFun
        (Arithmetic.residueChar w.1) (ringFun D w x) := by
  exact ringEquiv_frobenius D w x

-- The original-carrier function form used by native diagonal compatibility.
theorem ringFun_frobenius
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ringFun D w
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) =
      PadicWittRhoFrobenius.NativeFunction.frobeniusFun (Arithmetic.residueChar w.1)
        (ringFun D w x) := by
  exact ringFun_frobenius_native D w x


end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
