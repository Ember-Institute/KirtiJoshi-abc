import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTwistedQuotient

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TWISTED-QUOTIENT-COMPLETE
source: the actual complete common ring and the closed Frobenius/theta
subspaces constructed in the preceding Scene1 modules; Joshi II
`pr:teichmuller-lift-A` supplies the Banach-space quotient target.
fidelity: proves that both actual residual spaces and their quotient
spaces inherit complete Hausdorff additive topologies from the original
carrier. No finite-dimensionality or Tate classification is assumed.
boundary: Scene1/Derived; original carrier, topology and R5 remain.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTwistedQuotientComplete

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittEigenKernelTwistedComparison
open InitialThetaWittTwistedQuotient
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

instance fullComplete : CompleteSpace (Full D w) :=
  (fullKernel_isClosed D w).isComplete.completeSpace_coe

instance twistedComplete : CompleteSpace (Twisted D w) :=
  (twistedSubmodule_isClosed D w).isComplete.completeSpace_coe

theorem fullHausdorff : T2Space (Full D w) := inferInstance

theorem twistedHausdorff : T2Space (Twisted D w) := inferInstance

theorem fullCompleteSpace : CompleteSpace (Full D w) := inferInstance

theorem twistedCompleteSpace : CompleteSpace (Twisted D w) := inferInstance

end
end JoshiTeich.Act1Scene1.InitialThetaWittTwistedQuotientComplete
