import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalTatePrincipalLift
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalUnitPeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetTateKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PRINCIPAL-RATIONAL-LIFT
source: Joshi II `eq:tate-module-of-lubin-tate` and the period sequence
in the proof of `pr:teichmuller-lift-A`.
fidelity: transports the actual rational Tate principal-unit lift into the
constructed Frechet `phi=p` subspace and proves that its image is exactly the
Frechet rational Tate period map. The actual principal-period kernel theorem
then gives the corresponding evaluation-zero statement.
boundary: Scene1/Derived; this is an actual completion transport. It does not
identify the completion with paper `B`, define paper rho norms, or provide
H1e/BK, holomorphoid, paper representative, or theta-volume identities.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalRationalLift

open JoshiTeich.Prologue
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open InitialThetaWittRationalTatePeriod InitialThetaWittRationalTatePrincipalLift
open InitialThetaWittRationalTateSource
open InitialThetaWittFrechetComparison InitialThetaWittFrechetTateKernel
open InitialThetaWittFrechetPrincipalUnitPeriod
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

def frechetPrincipalRational (v : InitialThetaWittRationalTateSource.RationalTate D w) :
    InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w :=
  frechetPrincipalEigenLog D w
    (InitialThetaWittRationalTatePrincipalLift.rationalPrincipal D w v)

theorem frechetToActualEigen_frechetPrincipalRational (v :
    InitialThetaWittRationalTateSource.RationalTate D w) :
    InitialThetaWittFrechetTateKernel.frechetToActualEigen D w
        (frechetPrincipalRational D w v) =
      InitialThetaWittPrincipalUnitPeriod.eigenLogHom D w
        (Additive.ofMul
          (InitialThetaWittRationalTatePrincipalLift.rationalPrincipal D w v)) := by
  rw [frechetPrincipalRational,
    frechetPrincipalEigenLog_toActual D w]

theorem frechetToActualEigen_frechetEigenPeriodMap (v :
    InitialThetaWittRationalTateSource.RationalTate D w) :
    InitialThetaWittFrechetTateKernel.frechetToActualEigen D w
        (InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap D w v) =
      InitialThetaWittRationalTatePeriod.eigenPeriodMap D w v := by
  apply Subtype.ext
  change InitialThetaWittFrechetComparison.ringEquiv D w
      (InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap D w v) =
    InitialThetaWittRationalTatePeriod.periodMap D w v
  rw [InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap]
  change InitialThetaWittFrechetComparison.ringEquiv D w
      (InitialThetaWittFrechetTateKernel.frechetPeriodMap D w v) =
    InitialThetaWittRationalTatePeriod.periodMap D w v
  rw [InitialThetaWittFrechetTateKernel.frechetPeriodMap_apply]
  change (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w)
      ((InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
        (InitialThetaWittRationalTatePeriod.periodMap D w v)) =
    InitialThetaWittRationalTatePeriod.periodMap D w v
  rw [(InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).apply_symm_apply]

theorem frechetPrincipalRational_eq_frechetEigenPeriodMap (v :
    InitialThetaWittRationalTateSource.RationalTate D w) :
    frechetPrincipalRational D w v =
      InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap D w v := by
  apply InitialThetaWittFrechetTateKernel.frechetToActualEigen_injective D w
  rw [frechetToActualEigen_frechetPrincipalRational,
    frechetToActualEigen_frechetEigenPeriodMap]
  apply Subtype.ext
  exact InitialThetaWittRationalTatePrincipalLift.periodLog_rationalPrincipal D w v

theorem frechetPrincipalRational_evaluation (v :
    InitialThetaWittRationalTateSource.RationalTate D w) :
    InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w
        (frechetPrincipalRational D w v) = 0 := by
  rw [frechetPrincipalRational_eq_frechetEigenPeriodMap]
  change InitialThetaWittRationalTatePeriod.eigenEvaluation D w
      (InitialThetaWittFrechetTateKernel.frechetToActualEigen D w
        (InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap D w v)) = 0
  rw [frechetToActualEigen_frechetEigenPeriodMap]
  exact congrArg (fun f => f v)
    (InitialThetaWittRationalTatePeriod.eigenEvaluation_comp_periodMap D w)

theorem frechetPrincipalRational_mem_tateLine (v :
    InitialThetaWittRationalTateSource.RationalTate D w) :
    frechetPrincipalRational D w v ∈
      InitialThetaWittFrechetTateKernel.frechetTateLine D w := by
  rw [frechetPrincipalRational_eq_frechetEigenPeriodMap]
  exact ⟨v, rfl⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalRationalLift
