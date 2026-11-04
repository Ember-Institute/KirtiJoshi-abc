import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-SOURCE-EMBEDDING
source: Joshi II `se:ff-rings`, the bounded source inside a fixed-rho completion.
fidelity: records the underlying functions of the original source copy and
completion inclusion. Both remain the original maps with the original norm.
Original proof; Scene1/Derived; no paper B identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoCompletion

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

theorem sourceEquiv_apply (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    sourceEquiv D w ρ x = (show Source D w ρ from x) := rfl

theorem inclusion_apply (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    inclusion D w ρ x =
      ((show Source D w ρ from x) : UniformSpace.Completion (Source D w ρ)) := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoCompletion
