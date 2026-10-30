import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFullTateKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-TATE-KERNEL
source: Joshi II `pr:teichmuller-lift-A/B` and the actual Tate-period
sequence already proved on the common completion.
fidelity: transports the proved actual full theta-kernel identity and
rational Tate period range through the canonical continuous Padic-algebra
equivalence from the all-radius carrier to the Hausdorff Frechet completion.
No paper B marking, Galois action, or H1e/BK comparison is introduced.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this is an actual Frechet-completion transport,
not an identification with the paper's B.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateKernel

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison
open InitialThetaWittFrechetPadicComparison
open InitialThetaWittRationalTateSource InitialThetaWittRationalTatePeriod
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Scalars := Padic (Arithmetic.residueChar w.1)

def frechetPeriodMap : RationalTate D w →L[Scalars D w]
    InitialThetaWittFrechetComparison.Completed D w :=
  (continuousAlgEquiv D w).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (periodMap D w)

theorem frechetPeriodMap_apply (v : RationalTate D w) :
    frechetPeriodMap D w v =
      (continuousAlgEquiv D w).symm (periodMap D w v) := rfl

theorem frechetPeriodMap_injective : Function.Injective (frechetPeriodMap D w) := by
  intro x y h
  apply periodMap_injective D w
  have h' := congrArg (continuousAlgEquiv D w) h
  simpa only [frechetPeriodMap_apply, (continuousAlgEquiv D w).apply_symm_apply] using h'

theorem mem_fullKernel_iff_mem_frechetPeriodMap_range
    (x : InitialThetaWittFrechetComparison.Completed D w) :
    x ∈ InitialThetaWittFrechetFrobenius.fullKernel D w ↔
      x ∈ (frechetPeriodMap D w).range := by
  constructor
  · intro hx
    have hxactual :
        InitialThetaWittFrechetPadicComparison.algEquiv D w x ∈
          InitialThetaWittEigenKernelTwistedComparison.fullKernel D w :=
      (InitialThetaWittFrechetFrobenius.mem_fullKernel_iff D w x).mp hx
    have hxactual' :
        InitialThetaWittFrechetComparison.ringEquiv D w x ∈
          InitialThetaWittEigenKernelTwistedComparison.fullKernel D w := by
      simpa only [InitialThetaWittFrechetFrobenius.algEquiv_apply] using hxactual
    rw [InitialThetaWittFullTateKernel.fullKernel_eq_periodRange D w] at hxactual'
    obtain ⟨v, hv⟩ := hxactual'
    refine ⟨v, ?_⟩
    apply (InitialThetaWittFrechetComparison.ringEquiv D w).injective
    change (continuousAlgEquiv D w) (frechetPeriodMap D w v) =
      (continuousAlgEquiv D w) x
    rw [frechetPeriodMap_apply, (continuousAlgEquiv D w).apply_symm_apply]
    change periodMap D w v = (InitialThetaWittFrechetComparison.ringEquiv D w) x
    exact hv
  · rintro ⟨v, rfl⟩
    apply (InitialThetaWittFrechetFrobenius.mem_fullKernel_iff D w _).mpr
    have hv : periodMap D w v ∈
        InitialThetaWittEigenKernelTwistedComparison.fullKernel D w := by
      rw [InitialThetaWittFullTateKernel.fullKernel_eq_periodRange D w]
      exact ⟨v, rfl⟩
    change (continuousAlgEquiv D w) (frechetPeriodMap D w v) ∈
      InitialThetaWittEigenKernelTwistedComparison.fullKernel D w
    rw [frechetPeriodMap_apply, (continuousAlgEquiv D w).apply_symm_apply]
    exact hv

theorem fullKernel_eq_frechetPeriodMap_range :
    InitialThetaWittFrechetFrobenius.fullKernel D w =
      (frechetPeriodMap D w).range := by
  ext x
  exact mem_fullKernel_iff_mem_frechetPeriodMap_range D w x

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateKernel
