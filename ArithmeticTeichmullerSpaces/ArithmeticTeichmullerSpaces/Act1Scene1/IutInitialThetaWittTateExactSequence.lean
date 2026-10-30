import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFullTateKernel
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenEvaluationOpen
import Mathlib.Algebra.Exact.Basic

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-EXACT-SEQUENCE
source: Joshi II `eq:tate-module-of-lubin-tate` and the displayed
Banach exact sequence in `pr:teichmuller-lift-A` (935--958), citing
Fargues--Fontaine Proposition 4.5.14.
fidelity: the proved full actual Tate kernel gives exactness of the
original rational Tate period and eigen evaluation maps. The original
closed period embedding and open quotient evaluation give strict
topological exactness. The actual quotient evaluation has a continuous
linear inverse for the original untilt topology. Its fibers consist
of unique rational Tate translates. No kernel, classification or
inverse-continuity law is supplied as an input. Original proofs;
no reference implementation copied.
boundary: Scene1/Derived; the entire actual eigen space, actual tensor
Tate source, original quotient topology and untilt are retained.
Paper B and global holomorphoid/H1e/BK identities remain separate.
Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateExactSequence

open JoshiTeich.Prologue InitialThetaWittRationalTateSource
open InitialThetaWittRationalTatePeriod InitialThetaWittEigenRadiusDynamics
open InitialThetaWittTateBanachQuotient InitialThetaWittThetaBound
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem eigenEvaluation_exact : Function.Exact (eigenPeriodMap D w) (eigenEvaluation D w) := by
  apply LinearMap.exact_iff.mpr
  exact (InitialThetaWittTateBanachQuotientFullKernel.eigenKernel_eq_tateLine_iff_fullKernel_eq_periodMapRange
    D w).mpr (InitialThetaWittFullTateKernel.fullKernel_eq_periodRange D w)

theorem tatePeriodSequence_strictExact :
    Topology.IsClosedEmbedding (eigenPeriodMap D w) ∧
      Function.Exact (eigenPeriodMap D w) (eigenEvaluation D w) ∧
        IsOpenQuotientMap (eigenEvaluation D w) :=
  ⟨eigenPeriodMap_isClosedEmbedding D w, eigenEvaluation_exact D w,
    InitialThetaWittEigenEvaluationOpen.eigenEvaluation_isOpenQuotientMap D w⟩

def quotientEvaluationContinuousLinearEquiv :
    TateQuotient D w ≃L[Padic (Arithmetic.residueChar w.1)] Untilt D w := by
  let e : TateQuotient D w ≃ₗ[Padic (Arithmetic.residueChar w.1)] Untilt D w :=
    LinearEquiv.ofBijective (quotientEvaluation D w).toLinearMap
      ⟨InitialThetaWittFullTateKernel.quotientEvaluation_injective D w,
        quotientEvaluation_surjective D w⟩
  exact { e with
    continuous_toFun := (quotientEvaluation D w).continuous
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen
      (quotientEvaluation D w).continuous
      (InitialThetaWittEigenEvaluationOpen.quotientEvaluation_isOpenMap D w)).continuous_invFun }

theorem quotientEvaluationContinuousLinearEquiv_apply (x : TateQuotient D w) :
    quotientEvaluationContinuousLinearEquiv D w x = quotientEvaluation D w x := rfl

theorem quotientEvaluationContinuousLinearEquiv_mk (x : Eigen D w) :
    quotientEvaluationContinuousLinearEquiv D w (Submodule.Quotient.mk x) =
      eigenEvaluation D w x := rfl

theorem eigenEvaluation_eq_iff_existsUnique_period (x y : Eigen D w) :
    eigenEvaluation D w x = eigenEvaluation D w y ↔
      ∃! v : RationalTate D w, eigenPeriodMap D w v + y = x := by
  constructor
  · intro h
    have hz : eigenEvaluation D w (x - y) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨v, hv⟩ := (eigenEvaluation_exact D w (x - y)).mp hz
    have hv' : eigenPeriodMap D w v + y = x := eq_sub_iff_add_eq.mp hv
    refine ⟨v, hv', fun u hu => ?_⟩
    apply eigenPeriodMap_injective D w
    exact add_right_cancel (hu.trans hv'.symm)
  · rintro ⟨v, hv, _⟩
    have hz : eigenEvaluation D w (eigenPeriodMap D w v) = 0 :=
      congrArg (fun f => f v) (eigenEvaluation_comp_periodMap D w)
    have h := congrArg (eigenEvaluation D w) hv
    rw [map_add, hz, zero_add] at h
    exact h.symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateExactSequence
