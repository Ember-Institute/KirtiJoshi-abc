import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitLift
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalEvaluationSurjective
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalUnitPeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetTateKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PRINCIPAL-UNIT-LIFT
source: Joshi II `pr:teichmuller-lift-A`, `eq:tate-module-of-lubin-tate`,
and the multiplicative formal group description of `B^{phi=p}`.
fidelity: transports the existing actual principal-unit lift and its
convergent evaluation series through the canonical continuous algebra
equivalence into the constructed Frechet completion. The local principal
evaluation surjectivity is transported to the Frechet eigen evaluation.
boundary: Scene1/Derived; this remains an actual completion result and does
not identify the completion with paper `B`, define paper rho norms, or supply
H1e/BK, holomorphoid, or paper theta-locus identities.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalUnitLift

open JoshiTeich.Prologue
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitLift
open InitialThetaWittPrincipalUnitPeriod InitialThetaWittPrincipalEvaluationSurjective
open InitialThetaWittFrechetComparison InitialThetaWittFrechetTateKernel
open InitialThetaWittFrechetPrincipalUnitPeriod
open InitialThetaWittRationalTatePeriod
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Completed := InitialThetaWittFrechetComparison.Completed D w
abbrev Principal := InitialThetaWittPrincipalUnitDomain.Principal D w
abbrev UntilPrincipal := InitialThetaWittPrincipalUnitLift.UntilPrincipal D w

def frechetPrincipalLiftPeriod (z : UntilPrincipal D w) :
    InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w :=
  InitialThetaWittFrechetTateKernel.actualToFrechetEigen D w
    (InitialThetaWittPrincipalUnitLift.liftPeriod D w z)

theorem frechetPrincipalLiftPeriod_toActual (z : UntilPrincipal D w) :
    InitialThetaWittFrechetTateKernel.frechetToActualEigen D w
        (frechetPrincipalLiftPeriod D w z) =
      InitialThetaWittPrincipalUnitLift.liftPeriod D w z := by
  exact InitialThetaWittFrechetTateKernel.frechetToActualEigen_actualToFrechetEigen
    D w (InitialThetaWittPrincipalUnitLift.liftPeriod D w z)

theorem frechetPrincipalLiftPeriod_evaluation (z : UntilPrincipal D w) :
    InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w
        (frechetPrincipalLiftPeriod D w z) =
      InitialThetaWittRationalTatePeriod.eigenEvaluation D w
        (InitialThetaWittPrincipalUnitLift.liftPeriod D w z) := by
  rw [frechetPrincipalLiftPeriod,
    InitialThetaWittFrechetTateKernel.frechetEigenEvaluation_actualToFrechet]

theorem hasSum_frechetPrincipalLiftPeriod (z : UntilPrincipal D w) :
    HasSum (fun n : ℕ =>
      InitialThetaWittLogarithmSeries.logCoefficient D w n •
        (((z : (InitialThetaWittThetaBound.Untilt D w)ˣ) : InitialThetaWittThetaBound.Untilt D w) - 1) ^ n)
      (InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w
        (frechetPrincipalLiftPeriod D w z)) := by
  rw [frechetPrincipalLiftPeriod_evaluation]
  exact InitialThetaWittPrincipalUnitLift.hasSum_eigenEvaluation_liftPeriod D w z

theorem frechetPrincipalLiftPeriod_evaluation_eq_tsum (z : UntilPrincipal D w) :
    InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w
        (frechetPrincipalLiftPeriod D w z) =
      ∑' n : ℕ, InitialThetaWittLogarithmSeries.logCoefficient D w n •
        (((z : (InitialThetaWittThetaBound.Untilt D w)ˣ) : InitialThetaWittThetaBound.Untilt D w) - 1) ^ n :=
  (hasSum_frechetPrincipalLiftPeriod D w z).tsum_eq.symm

theorem exists_frechetEigenPeriod_logarithm (z : UntilPrincipal D w) :
    ∃ v : InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w,
      HasSum (fun n : ℕ =>
        InitialThetaWittLogarithmSeries.logCoefficient D w n •
          (((z : (InitialThetaWittThetaBound.Untilt D w)ˣ) : InitialThetaWittThetaBound.Untilt D w) - 1) ^ n)
        (InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w v) :=
  ⟨frechetPrincipalLiftPeriod D w z, hasSum_frechetPrincipalLiftPeriod D w z⟩

theorem frechetPrincipalEvaluation_surjective :
    Function.Surjective (fun u : Principal D w =>
      InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w
        (frechetPrincipalEigenLog D w u)) := by
  intro y
  obtain ⟨a, ha⟩ :=
    InitialThetaWittPrincipalEvaluationSurjective.principalEvaluationHom_surjective D w y
  refine ⟨a.toMul, ?_⟩
  change InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w
      (frechetPrincipalEigenLog D w a.toMul) = y
  rw [frechetPrincipalEigenLog_evaluation D w a.toMul]
  change InitialThetaWittThetaEvaluation.evaluation D w
      (periodLog D w a.toMul) = y at ha
  exact ha

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalUnitLift
