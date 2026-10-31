import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetTateLogTransport
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithmInjective

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-TATE-LOG-EIGEN-HOM
source: Joshi II `se:ff-rings`, `eq:tate-module-of-lubin-tate`, and
`pr:teichmuller-lift-A/B`.
fidelity: packages the transported actual Tate logarithm into an additive
homomorphism on the Tate inverse-limit source. Its value, actual retraction,
and injectivity are inherited from the actual additive Tate period map.
boundary: Scene1/Derived; this is an actual completion transport and does not
identify the completion with paper `B`, define rho norms, or provide H1e/BK,
holomorphoid, or paper period identities.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateLogEigenHom

open JoshiTeich.Prologue
open InitialThetaWittFrechetTateLogProducer InitialThetaWittFrechetTateKernel
open InitialThetaWittFrechetTateLogTransport
open InitialThetaWittAdditiveTatePeriod InitialThetaWittTateLogarithmInjective
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Tate := InitialThetaWittFrechetTateLogProducer.Tate D w
abbrev Completed := InitialThetaWittFrechetComparison.Completed D w

def frechetTateLogEigenHom : Additive (Tate D w) →+
    InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w :=
  (InitialThetaWittFrechetTateKernel.actualToFrechetEigen D w).toLinearMap.toAddMonoidHom.comp
    (InitialThetaWittAdditiveTatePeriod.tateLogEigenHom D w)

theorem frechetTateLogEigenHom_apply (t : Additive (Tate D w)) :
    frechetTateLogEigenHom D w t =
      frechetTateLogEigen D w t.toMul := by
  apply Subtype.ext
  rfl

theorem frechetToActualEigen_frechetTateLogEigenHom (t : Additive (Tate D w)) :
    InitialThetaWittFrechetTateKernel.frechetToActualEigen D w
        (frechetTateLogEigenHom D w t) =
      InitialThetaWittAdditiveTatePeriod.tateLogEigenHom D w t := by
  rw [frechetTateLogEigenHom]
  exact InitialThetaWittFrechetTateKernel.frechetToActualEigen_actualToFrechetEigen
    D w (InitialThetaWittAdditiveTatePeriod.tateLogEigenHom D w t)

theorem frechetTateLogEigenHom_value (t : Tate D w) :
    (frechetTateLogEigenHom D w (Additive.ofMul t) : Completed D w) =
      frechetTateLog D w t := by
  rw [frechetTateLogEigenHom_apply,
    frechetTateLogEigen_value]
  simp only [toMul_ofMul]

theorem frechetTateLogEigenHom_injective :
    Function.Injective (frechetTateLogEigenHom D w) := by
  intro x y h
  have h' := congrArg
    (InitialThetaWittFrechetTateKernel.frechetToActualEigen D w) h
  rw [frechetToActualEigen_frechetTateLogEigenHom D w x,
    frechetToActualEigen_frechetTateLogEigenHom D w y] at h'
  exact InitialThetaWittTateLogarithmInjective.tateLogEigenHom_injective D w h'

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateLogEigenHom
