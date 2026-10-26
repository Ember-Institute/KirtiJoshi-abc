import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateBanachQuotientFullKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-BANACH-QUOTIENT-EQUIV
source: Joshi II `pr:teichmuller-lift-A`, its exact Tate-period sequence,
and the actual full-kernel comparison proved in Scene1.
fidelity: under the explicit full-kernel equality, upgrades the actual
surjective quotient evaluation to a Q_p-linear equivalence with the
original untilt. The converse records that existence of this upgrade
forces the same kernel equality.
boundary: Scene1/Derived; the full-kernel equality remains an explicit
condition and is not asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateBanachQuotientEquiv

open JoshiTeich.Prologue InitialThetaWittRationalTatePeriod
open InitialThetaWittTateBanachQuotient
open InitialThetaWittTateBanachQuotientFullKernel
open InitialThetaWittEigenKernelTwistedComparison
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

noncomputable def quotientEvaluationLinearEquiv
    (h : fullKernel D w = (periodMap D w).range) :
    TateQuotient D w ≃ₗ[Padic (Arithmetic.residueChar w.1)]
      InitialThetaWittThetaBound.Untilt D w :=
  LinearEquiv.ofBijective (quotientEvaluation D w).toLinearMap
    ⟨(quotientEvaluation_injective_iff_fullKernel_eq_periodMapRange D w).mpr h,
      quotientEvaluation_surjective D w⟩

theorem quotientEvaluationLinearEquiv_apply
    (h : fullKernel D w = (periodMap D w).range)
    (x : TateQuotient D w) :
    quotientEvaluationLinearEquiv D w h x = quotientEvaluation D w x := by
  rfl

theorem quotientEvaluationLinearEquiv_exists_iff :
    (∃ e : TateQuotient D w ≃ₗ[Padic (Arithmetic.residueChar w.1)]
      InitialThetaWittThetaBound.Untilt D w,
      ∀ x, e x = quotientEvaluation D w x) ↔
      fullKernel D w = (periodMap D w).range := by
  constructor
  · rintro ⟨e, he⟩
    apply (quotientEvaluation_injective_iff_fullKernel_eq_periodMapRange D w).mp
    intro x y hxy
    apply e.injective
    rw [he, he, hxy]
  · intro h
    exact ⟨quotientEvaluationLinearEquiv D w h,
      quotientEvaluationLinearEquiv_apply D w h⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateBanachQuotientEquiv
