import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoCompletionComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoSourceEmbedding
import ArithmeticTeichmullerSpaces.Act1Scene1.CompletionMapComparison
/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-COMPLETION-INCLUSION-SOURCE
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the original
bounded subring inside each completion.
fidelity: carries the original actual bounded inclusion through the existing
completion equivalence to the native standard completion coe of the saved
source function. The original map, radius and both completions are retained.
Original proof; Scene1/Derived; Prologue R5 unchanged.
boundary: identifying this coe with the original standard bounded inclusion
and restricting the product equivalence to the common closure are separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoCompletionComparison
open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrimeInclusionSource : Fact (Arithmetic.residueChar w.1).Prime := ⟨Arithmetic.residueChar_prime w.1⟩
theorem completedRingEquiv_inclusion_to_sourceFun (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w) :
    completedRingEquiv D w ρ
        (InitialThetaWittRhoCompletion.inclusion D w (actualRadius D w ρ) x) =
      (sourceFun D w ρ
        (show InitialThetaWittRhoCompletion.Source D w (actualRadius D w ρ) from x) :
        UniformSpace.Completion (PadicWittRhoCompletion.Source (Arithmetic.residueChar w.1) ρ)) :=
  (congrArg (fun z : UniformSpace.Completion
      (InitialThetaWittRhoCompletion.Source D w (actualRadius D w ρ)) =>
        completedRingEquiv D w ρ z)
      (InitialThetaWittRhoCompletion.inclusion_apply D w (actualRadius D w ρ) x)).trans
    (CompletionMapComparison.change_source_map
      (completedRingEquiv_coe_native D w ρ) (sourceRingEquiv_apply D w ρ)
      (show InitialThetaWittRhoCompletion.Source D w (actualRadius D w ρ) from x))
end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoCompletionComparison
