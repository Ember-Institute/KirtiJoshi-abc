import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetTateLogProducer
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetTateKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-TATE-LOG-TRANSPORT
source: Joshi II `se:ff-rings`, `eq:tate-module-of-lubin-tate` and
`pr:teichmuller-lift-A/B`, transported through the canonical all-radius
completion comparison.
fidelity: pulls the actual all-radius Tate-log convergence domain and its
HasSum producer back to the canonical continuous Frechet completion. The
same actual Tate logarithm transports into the Frechet `phi=p` submodule.
No new convergence or period identity is assumed.
boundary: Scene1/Derived; this identifies the transported actual Tate-log
and its eigen equation on the constructed completion, not the paper's B,
paper rho norms, H1e/BK, or a global holomorphoid. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateLogTransport

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison InitialThetaWittFrechetPadicComparison
open InitialThetaWittFrechetTateLogProducer InitialThetaWittFrechetTateKernel
open InitialThetaWittTateLogarithm InitialThetaWittLogarithmSeries
open InitialThetaWittAdditiveTatePeriod
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
abbrev ActualCarrier := InitialThetaWittFrechetTateLogProducer.Carrier D w
abbrev Tate := InitialThetaWittFrechetTateLogProducer.Tate D w

def FrechetDomain :=
  {x : Completed D w //
    InitialThetaWittLogarithmMultiplication.InDomain D w
      (InitialThetaWittFrechetPadicComparison.algEquiv D w x)}

def frechetDomainOfActual (x : InitialThetaWittFrechetTateLogProducer.Domain D w) :
    FrechetDomain D w :=
  ⟨(InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm x.1,
    by
      change InitialThetaWittLogarithmMultiplication.InDomain D w
        ((InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w)
          ((InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm x.1))
      simpa only [(InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).apply_symm_apply]
        using x.2⟩

theorem frechetDomainOfActual_apply
    (x : InitialThetaWittFrechetTateLogProducer.Domain D w) :
    (frechetDomainOfActual D w x).1 =
      (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm x.1 := rfl

def frechetLogTerm (x : FrechetDomain D w) (n : ℕ) : Completed D w :=
  (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
    (InitialThetaWittLogarithmSeries.logTerm D w
      (InitialThetaWittFrechetPadicComparison.algEquiv D w x.1) n)

def frechetLog (x : FrechetDomain D w) : Completed D w :=
  (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
    (InitialThetaWittLogarithmSeries.logOneAdd D w
      (InitialThetaWittFrechetPadicComparison.algEquiv D w x.1))

theorem frechetLog_hasSum (x : FrechetDomain D w) :
    HasSum (fun n => frechetLogTerm D w x n) (frechetLog D w x) := by
  let e := (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).toContinuousLinearEquiv
  let eAdd : ActualCarrier D w →+ Completed D w := e.symm.toContinuousLinearMap.toAddMonoidHom
  have heAdd : Continuous eAdd := e.symm.continuous
  exact (InitialThetaWittFrechetTateLogProducer.logOnDomain_hasSum D w
    ⟨InitialThetaWittFrechetPadicComparison.algEquiv D w x.1, x.2⟩).map
      eAdd heAdd

def frechetTateInput (t : Tate D w) : FrechetDomain D w :=
  frechetDomainOfActual D w (InitialThetaWittFrechetTateLogProducer.tateInput D w t)

def frechetTateLog (t : Tate D w) : Completed D w :=
  (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
    (InitialThetaWittTateLogarithm.tateLog D w t)

def frechetTateLogTerm (t : Tate D w) (n : ℕ) : Completed D w :=
  (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
    (InitialThetaWittLogarithmSeries.logTerm D w
      (InitialThetaWittTateLogarithm.coordinate D w t) n)

theorem frechetContinuousAlgEquiv_apply (x : Completed D w) :
    InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w x =
      InitialThetaWittFrechetComparison.ringEquiv D w x := rfl

theorem frechetTateLog_eq_transport (t : Tate D w) :
    frechetTateLog D w t =
      (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
        (InitialThetaWittTateLogarithm.tateLog D w t) := by
  rfl

theorem frechetTateLog_hasSum (t : Tate D w) :
    HasSum (fun n => frechetTateLogTerm D w t n)
      (frechetTateLog D w t) :=
  let e := (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).toContinuousLinearEquiv
  let eAdd : ActualCarrier D w →+ Completed D w := e.symm.toContinuousLinearMap.toAddMonoidHom
  have heAdd : Continuous eAdd := e.symm.continuous
  (InitialThetaWittTateLogarithm.hasSum_tateLog D w t).map eAdd heAdd

theorem frechetTateLog_mem_frobeniusPrime (t : Tate D w) :
    frechetTateLog D w t ∈ InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w := by
  change InitialThetaWittFrechetPadicComparison.algEquiv D w
      (frechetTateLog D w t) ∈
        InitialThetaWittAdditiveTatePeriod.frobeniusPrimeSubmodule D w
  rw [frechetTateLog_eq_transport]
  change (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w)
      ((InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).symm
        (InitialThetaWittTateLogarithm.tateLog D w t)) ∈ _
  rw [(InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).apply_symm_apply]
  exact InitialThetaWittAdditiveTatePeriod.tateLog_mem_frobeniusPrime D w t

theorem frechetTateLog_frobenius_eq_prime_smul (t : Tate D w) :
    InitialThetaWittFrechetFrobenius.frobeniusEquiv D w (frechetTateLog D w t) =
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) •
        frechetTateLog D w t := by
  apply (InitialThetaWittFrechetPadicComparison.algEquiv D w).injective
  calc
    _ = InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
        (InitialThetaWittTateLogarithm.tateLog D w t) := by
          rw [InitialThetaWittFrechetFrobenius.algEquiv_apply,
            InitialThetaWittFrechetFrobenius.frobeniusEquiv_apply,
            frechetTateLog_eq_transport,
            ← frechetContinuousAlgEquiv_apply D w,
            (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).apply_symm_apply]
    _ = (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) •
        InitialThetaWittTateLogarithm.tateLog D w t := by
          exact InitialThetaWittTateFrobeniusEigen.frobenius_tateLog_eq_prime_smul D w t
    _ = (InitialThetaWittFrechetPadicComparison.algEquiv D w)
        ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) •
          frechetTateLog D w t) := by
          rw [frechetTateLog_eq_transport, map_smul,
            InitialThetaWittFrechetFrobenius.algEquiv_apply,
            ← frechetContinuousAlgEquiv_apply D w,
            (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).apply_symm_apply]

def frechetTateLogEigen (t : Tate D w) :
    InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w :=
  ⟨frechetTateLog D w t, frechetTateLog_mem_frobeniusPrime D w t⟩

theorem frechetTateLogEigen_value (t : Tate D w) :
    (frechetTateLogEigen D w t : Completed D w) = frechetTateLog D w t := rfl

theorem frechetTateLogEigen_toActual (t : Tate D w) :
    InitialThetaWittFrechetTateKernel.frechetToActualEigen D w
        (frechetTateLogEigen D w t) =
      InitialThetaWittAdditiveTatePeriod.tateLogEigenHom D w
        (Additive.ofMul t) := by
  apply Subtype.ext
  change InitialThetaWittFrechetComparison.ringEquiv D w
      (frechetTateLog D w t) =
    InitialThetaWittAdditiveTatePeriod.tateLogHom D w (Additive.ofMul t)
  rw [frechetTateLog_eq_transport,
    ← frechetContinuousAlgEquiv_apply D w,
    (InitialThetaWittFrechetPadicComparison.continuousAlgEquiv D w).apply_symm_apply]
  rfl

theorem frechetTateLogEigen_injective :
    Function.Injective (fun t : Tate D w => frechetTateLogEigen D w t) := by
  intro t u h
  apply InitialThetaWittTateLogarithmInjective.tateLogEigenHom_injective D w
  have h' := congrArg
    (InitialThetaWittFrechetTateKernel.frechetToActualEigen D w) h
  rw [frechetTateLogEigen_toActual D w t,
    frechetTateLogEigen_toActual D w u] at h'
  exact h'

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateLogTransport
