import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoCompletionInclusionSource
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoSourceEmbedding
/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-COMPLETION-INCLUSION-TARGET
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the original
bounded subring inside the independent standard rho completion.
fidelity: identifies the coe of the saved source map with the native
standard inclusion function. Its p-only equality with the original named
inclusion is proved separately before specializing to actual data.
Both the standard completion and bounded map retain their original values.
Original proof; Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoCompletionComparison
open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrimeInclusionTarget : Fact (Arithmetic.residueChar w.1).Prime := ⟨Arithmetic.residueChar_prime w.1⟩
theorem sourceFun_coe_inclusionFun (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (sourceFun D w ρ
      (show InitialThetaWittRhoCompletion.Source D w (actualRadius D w ρ) from x) :
      UniformSpace.Completion (PadicWittRhoCompletion.Source (Arithmetic.residueChar w.1) ρ)) =
        PadicWittRhoCompletion.inclusionFun (Arithmetic.residueChar w.1) ρ
          (InitialThetaPadicBoundedWittComparison.ringFun D w x) :=
  congrArg (fun y : PadicWittRhoCompletion.Source (Arithmetic.residueChar w.1) ρ =>
      (y : UniformSpace.Completion (PadicWittRhoCompletion.Source (Arithmetic.residueChar w.1) ρ)))
      (sourceFun_fromRaw D w ρ x)

theorem completedRingEquiv_inclusionFun (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    completedRingEquiv D w ρ
        (InitialThetaWittRhoCompletion.inclusion D w (actualRadius D w ρ) x) =
      PadicWittRhoCompletion.inclusionFun (Arithmetic.residueChar w.1) ρ
        (InitialThetaPadicBoundedWittComparison.ringFun D w x) :=
  (completedRingEquiv_inclusion_to_sourceFun D w ρ x).trans
    (sourceFun_coe_inclusionFun D w ρ x)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoCompletionComparison
