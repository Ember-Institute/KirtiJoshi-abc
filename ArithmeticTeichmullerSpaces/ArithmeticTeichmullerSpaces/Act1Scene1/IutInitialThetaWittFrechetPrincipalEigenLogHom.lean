import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalUnitPeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalUnitLift
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitInjective
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalEvaluationSurjective

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PRINCIPAL-EIGEN-LOG-HOM
source: Joshi II `pr:teichmuller-lift-A`, `eq:tate-module-of-lubin-tate`,
and the multiplicative formal group description of `B^{phi=p}`.
fidelity: packages the transported principal-unit eigen logarithm into an
additive homomorphism, proves its actual retraction and injectivity, and
identifies its evaluation with the existing actual principal evaluation hom.
The local evaluation surjectivity therefore transfers to the constructed
Frechet completion.
boundary: Scene1/Derived; this is an actual completion transport and does not
identify paper `B`, define rho norms, or supply H1e/BK, holomorphoid, or paper
theta-volume identities.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalEigenLogHom

open JoshiTeich.Prologue
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open InitialThetaWittPrincipalUnitInjective InitialThetaWittPrincipalEvaluationSurjective
open InitialThetaWittFrechetComparison InitialThetaWittFrechetTateKernel
open InitialThetaWittFrechetPrincipalUnitPeriod
open InitialThetaWittFrechetPrincipalUnitLift
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Principal := InitialThetaWittPrincipalUnitDomain.Principal D w
abbrev Untilt := InitialThetaWittThetaBound.Untilt D w

def frechetPrincipalEigenLogHom : Additive (Principal D w) →+
    InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w :=
  (InitialThetaWittFrechetTateKernel.actualToFrechetEigen D w).toLinearMap.toAddMonoidHom.comp
    (InitialThetaWittPrincipalUnitPeriod.eigenLogHom D w)

theorem frechetPrincipalEigenLogHom_apply (u : Additive (Principal D w)) :
    frechetPrincipalEigenLogHom D w u =
      frechetPrincipalEigenLog D w u.toMul := by
  apply Subtype.ext
  rfl

theorem frechetToActualEigen_frechetPrincipalEigenLogHom
    (u : Additive (Principal D w)) :
    InitialThetaWittFrechetTateKernel.frechetToActualEigen D w
        (frechetPrincipalEigenLogHom D w u) =
      InitialThetaWittPrincipalUnitPeriod.eigenLogHom D w u := by
  rw [frechetPrincipalEigenLogHom]
  exact InitialThetaWittFrechetTateKernel.frechetToActualEigen_actualToFrechetEigen
    D w (InitialThetaWittPrincipalUnitPeriod.eigenLogHom D w u)

theorem frechetPrincipalEigenLogHom_injective :
    Function.Injective (frechetPrincipalEigenLogHom D w) := by
  intro u v h
  have h' := congrArg
    (InitialThetaWittFrechetTateKernel.frechetToActualEigen D w) h
  rw [frechetToActualEigen_frechetPrincipalEigenLogHom D w u,
    frechetToActualEigen_frechetPrincipalEigenLogHom D w v] at h'
  exact InitialThetaWittPrincipalUnitInjective.eigenLogHom_injective D w h'

def frechetPrincipalEvaluationHom : Additive (Principal D w) →+ Untilt D w :=
  (InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w).toLinearMap.toAddMonoidHom.comp
    (frechetPrincipalEigenLogHom D w)

theorem frechetPrincipalEvaluationHom_apply (u : Additive (Principal D w)) :
    frechetPrincipalEvaluationHom D w u =
      InitialThetaWittPrincipalEvaluationSurjective.principalEvaluationHom D w u := by
  change InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w
      (frechetPrincipalEigenLogHom D w u) = _
  rw [frechetPrincipalEigenLogHom_apply]
  rw [frechetPrincipalEigenLog_evaluation D w u.toMul]
  rfl

theorem frechetPrincipalEvaluationHom_surjective :
    Function.Surjective (frechetPrincipalEvaluationHom D w) := by
  intro y
  obtain ⟨u, hu⟩ :=
    InitialThetaWittPrincipalEvaluationSurjective.principalEvaluationHom_surjective D w y
  exact ⟨u, (frechetPrincipalEvaluationHom_apply D w u).trans hu⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalEigenLogHom
