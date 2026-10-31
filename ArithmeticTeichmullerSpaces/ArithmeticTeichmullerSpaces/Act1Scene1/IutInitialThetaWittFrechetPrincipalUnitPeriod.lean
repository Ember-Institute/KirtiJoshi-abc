import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitPeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitInjective
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetTateLogTransport

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PRINCIPAL-UNIT-PERIOD
source: Joshi II `pr:teichmuller-lift-A` and the multiplicative formal
group description of `B^{phi=p}`, transported through the actual Frechet
completion comparison.
fidelity: transports the actual principal-unit period logarithm, its
convergent all-radius series, its `phi=p` eigen equation, and its untilt
evaluation through the canonical continuous algebra equivalence. The
transported value is identified with the existing actual eigen logarithm.
boundary: Scene1/Derived; this does not identify the completion with paper
`B`, define paper rho norms, or supply H1e/BK or global holomorphoid laws.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalUnitPeriod

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison InitialThetaWittFrechetPadicComparison
open InitialThetaWittFrechetTateLogTransport
open InitialThetaWittFrechetTateKernel
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open InitialThetaWittRationalTatePeriod
open InitialThetaWittLogarithmSeries InitialThetaWittAdditiveTatePeriod
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

def frechetPrincipalPeriodLog (u : Principal D w) : Completed D w :=
  (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
    (periodLog D w u)

def frechetPrincipalLogTerm (u : Principal D w) (n : ℕ) : Completed D w :=
  (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
    (logTerm D w (coordinate D w u) n)

theorem frechetPrincipalPeriodLog_hasSum (u : Principal D w) :
    HasSum (fun n => frechetPrincipalLogTerm D w u n)
      (frechetPrincipalPeriodLog D w u) := by
  let e := (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).toContinuousLinearEquiv
  let eAdd : InitialThetaWittFrechetComparison.Carrier D w →+ Completed D w :=
    e.symm.toContinuousLinearMap.toAddMonoidHom
  have heAdd : Continuous eAdd := e.symm.continuous
  exact (hasSum_periodLog D w u).map eAdd heAdd

def frechetPrincipalEigenLog (u : Principal D w) :
    InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w := by
  refine ⟨frechetPrincipalPeriodLog D w u, ?_⟩
  change InitialThetaWittFrechetPadicComparison.algEquiv D w
      (frechetPrincipalPeriodLog D w u) ∈ frobeniusPrimeSubmodule D w
  change (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w)
      ((InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
        (periodLog D w u)) ∈ _
  rw [(InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).apply_symm_apply]
  exact (eigenLogHom D w (Additive.ofMul u)).property

theorem frechetPrincipalEigenLog_value (u : Principal D w) :
    (frechetPrincipalEigenLog D w u : Completed D w) =
      frechetPrincipalPeriodLog D w u := rfl

theorem frechetPrincipalEigenLog_toActual (u : Principal D w) :
    InitialThetaWittFrechetTateKernel.frechetToActualEigen D w
        (frechetPrincipalEigenLog D w u) =
      eigenLogHom D w (Additive.ofMul u) := by
  apply Subtype.ext
  change InitialThetaWittFrechetComparison.ringEquiv D w
      (frechetPrincipalPeriodLog D w u) = periodLog D w u
  rw [frechetPrincipalPeriodLog,
    ← InitialThetaWittFrechetTateLogTransport.frechetContinuousAlgEquiv_apply D w,
    (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).apply_symm_apply]

theorem frechetPrincipalEigenLog_evaluation (u : Principal D w) :
    frechetEigenEvaluation D w (frechetPrincipalEigenLog D w u) =
      InitialThetaWittThetaEvaluation.evaluation D w (periodLog D w u) := by
  change eigenEvaluation D w
    (frechetToActualEigen D w (frechetPrincipalEigenLog D w u)) =
      InitialThetaWittThetaEvaluation.evaluation D w (periodLog D w u)
  rw [frechetPrincipalEigenLog_toActual D w]
  rfl

theorem frechetPrincipalEigenLog_injective :
    Function.Injective (fun u : Principal D w => frechetPrincipalEigenLog D w u) := by
  intro u v h
  have h' := congrArg
    (InitialThetaWittFrechetTateKernel.frechetToActualEigen D w) h
  rw [frechetPrincipalEigenLog_toActual D w u,
    frechetPrincipalEigenLog_toActual D w v] at h'
  apply InitialThetaWittPrincipalUnitInjective.periodLogHom_injective D w
  exact congrArg Subtype.val h'

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalUnitPeriod
