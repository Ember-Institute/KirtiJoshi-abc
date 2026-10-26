import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenBanach
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenEvaluationSurjective
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-BANACH-QUOTIENT
source: Joshi II `pr:teichmuller-lift-A`, the displayed sequence
T_y tensor Q_p -> B^{phi=p} -> K_y -> 0.
fidelity: takes the quotient of the entire actual phi=p Banach space
by its proved actual rational Tate period line. That line is closed,
so the quotient has a genuine complete standard-Q_p normed-space
structure. Actual theta evaluation descends to a continuous linear
surjection onto the original untilt. Its injectivity is proved equivalent
to the still-open full kernel identity, rather than assumed.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the original period carrier, uniformity and
scalar actions are retained. No full kernel identity or injectivity of
the quotient comparison is supplied as input. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateBanachQuotient

open JoshiTeich.Prologue InitialThetaWittEigenRadiusDynamics
open InitialThetaWittEigenBanach InitialThetaWittRationalTatePeriod
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def tateLine : Submodule (Padic (Arithmetic.residueChar w.1)) (Eigen D w) :=
  (eigenPeriodMap D w).range

instance tateLineIsClosed : IsClosed (tateLine D w : Set (Eigen D w)) :=
  (eigenPeriodMap_isClosedEmbedding D w).isClosed_range

abbrev TateQuotient := Eigen D w ⧸ tateLine D w

theorem quotient_banach_complete : CompleteSpace (TateQuotient D w) := inferInstance

theorem quotient_norm_smul (a : Padic (Arithmetic.residueChar w.1)) (x : TateQuotient D w) :
    ‖a • x‖ = ‖a‖ * ‖x‖ := norm_smul a x

theorem quotient_mk_norm_le (x : Eigen D w) :
    ‖(Submodule.Quotient.mk x : TateQuotient D w)‖ ≤ ‖x‖ :=
  Submodule.Quotient.norm_mk_le (tateLine D w) x

theorem tateLine_le_kernel : tateLine D w ≤ (eigenEvaluation D w).ker := by
  rintro x ⟨v, rfl⟩
  have h := congrArg (fun f => f v) (eigenEvaluation_comp_periodMap D w)
  exact h

def quotientEvaluation : TateQuotient D w →L[Padic (Arithmetic.residueChar w.1)]
    InitialThetaWittThetaBound.Untilt D w :=
  (tateLine D w).liftQL (eigenEvaluation D w) (tateLine_le_kernel D w)

theorem quotientEvaluation_mk (x : Eigen D w) :
    quotientEvaluation D w (Submodule.Quotient.mk x) = eigenEvaluation D w x := rfl

theorem quotientEvaluation_surjective : Function.Surjective (quotientEvaluation D w) := by
  intro y
  obtain ⟨x, hx⟩ := InitialThetaWittEigenEvaluationSurjective.eigenEvaluation_surjective D w y
  exact ⟨Submodule.Quotient.mk x, (quotientEvaluation_mk D w x).trans hx⟩

theorem quotientEvaluation_injective_iff :
    Function.Injective (quotientEvaluation D w) ↔ (eigenEvaluation D w).ker = tateLine D w := by
  constructor
  · intro hinj
    apply le_antisymm _ (tateLine_le_kernel D w)
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero (tateLine D w)).mp
    apply hinj
    rw [quotientEvaluation_mk, map_zero]
    exact hx
  · intro hker
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot (tateLine D w) (eigenEvaluation D w).toLinearMap
      (tateLine_le_kernel D w) hker.le

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateBanachQuotient
