import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittUntiltBanachView
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateBanachQuotient
import Mathlib.Analysis.Normed.Operator.Banach

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-EVALUATION-OPEN
source: Joshi II `pr:teichmuller-lift-A`, the canonical evaluation in
the displayed period sequence; the Banach open mapping theorem.
fidelity: actual theta is contractive between the proved standard-Q_p
Banach norms and is surjective. The open mapping theorem makes it open;
the explicit norm-view equivalence returns the result to the original
untilt topology. The same holds for the actual Tate quotient comparison.
Obtains a uniform bound for actual period preimages in terms of the
proved calibration power of the original untilt field norm.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no kernel identity or injectivity of the Tate
quotient comparison is assumed or asserted. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenEvaluationOpen

open JoshiTeich.Prologue InitialThetaWittThetaBound
open InitialThetaWittEigenRadiusDynamics InitialThetaWittEigenBanach
open InitialThetaWittUntiltBanachView InitialThetaWittRationalTatePeriod
open InitialThetaWittTateBanachQuotient
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def normalizedEigenEvaluation : Eigen D w →L[Padic (Arithmetic.residueChar w.1)] NormView D w :=
  (originalContinuousLinearEquiv D w).symm.toContinuousLinearMap.comp (eigenEvaluation D w)

theorem normalizedEigenEvaluation_apply (x : Eigen D w) :
    normalizedEigenEvaluation D w x = (originalContinuousLinearEquiv D w).symm (eigenEvaluation D w x) := rfl

theorem normalizedEigenEvaluation_surjective : Function.Surjective (normalizedEigenEvaluation D w) :=
  (originalContinuousLinearEquiv D w).symm.surjective.comp
    (InitialThetaWittEigenEvaluationSurjective.eigenEvaluation_surjective D w)

theorem norm_normalizedEigenEvaluation_le (x : Eigen D w) :
    ‖normalizedEigenEvaluation D w x‖ ≤ ‖x‖ := by
  rw [normalizedEigenEvaluation_apply, norm_originalInverse, norm_eq_coordinate_power]
  exact Real.rpow_le_rpow (norm_nonneg _)
    (InitialThetaWittThetaEvaluation.evaluation_norm_le D w x.val)
    (InitialThetaWittScalarCalibration.exponent_pos D w (radius D w)).le

theorem eigenEvaluation_isOpenMap : IsOpenMap (eigenEvaluation D w) := by
  have h := (originalContinuousLinearEquiv D w).toHomeomorph.isOpenMap.comp
    ((normalizedEigenEvaluation D w).isOpenMap (normalizedEigenEvaluation_surjective D w))
  change IsOpenMap (fun x => originalContinuousLinearEquiv D w (normalizedEigenEvaluation D w x)) at h
  simpa only [normalizedEigenEvaluation_apply, (originalContinuousLinearEquiv D w).apply_symm_apply] using h

theorem eigenEvaluation_isOpenQuotientMap : IsOpenQuotientMap (eigenEvaluation D w) :=
  ⟨InitialThetaWittEigenEvaluationSurjective.eigenEvaluation_surjective D w,
    (eigenEvaluation D w).continuous, eigenEvaluation_isOpenMap D w⟩

def normalizedQuotientEvaluation : TateQuotient D w →L[Padic (Arithmetic.residueChar w.1)] NormView D w :=
  (originalContinuousLinearEquiv D w).symm.toContinuousLinearMap.comp (quotientEvaluation D w)

theorem normalizedQuotientEvaluation_apply (x : TateQuotient D w) :
    normalizedQuotientEvaluation D w x =
      (originalContinuousLinearEquiv D w).symm (quotientEvaluation D w x) := rfl

theorem normalizedQuotientEvaluation_surjective : Function.Surjective (normalizedQuotientEvaluation D w) :=
  (originalContinuousLinearEquiv D w).symm.surjective.comp (quotientEvaluation_surjective D w)

theorem quotientEvaluation_isOpenMap : IsOpenMap (quotientEvaluation D w) := by
  have h := (originalContinuousLinearEquiv D w).toHomeomorph.isOpenMap.comp
    ((normalizedQuotientEvaluation D w).isOpenMap (normalizedQuotientEvaluation_surjective D w))
  change IsOpenMap (fun x => originalContinuousLinearEquiv D w (normalizedQuotientEvaluation D w x)) at h
  simpa only [normalizedQuotientEvaluation_apply, (originalContinuousLinearEquiv D w).apply_symm_apply] using h

theorem quotientEvaluation_isOpenQuotientMap : IsOpenQuotientMap (quotientEvaluation D w) :=
  ⟨quotientEvaluation_surjective D w, (quotientEvaluation D w).continuous, quotientEvaluation_isOpenMap D w⟩

theorem exists_period_preimage_bound : ∃ C : ℝ, 0 < C ∧ ∀ y : Untilt D w,
    ∃ x : Eigen D w, eigenEvaluation D w x = y ∧
      ‖x‖ ≤ C * ‖y‖ ^ InitialThetaWittScalarCalibration.exponent D w (radius D w) := by
  obtain ⟨C, hC, h⟩ := ContinuousLinearMap.exists_preimage_norm_le
    (normalizedEigenEvaluation D w) (normalizedEigenEvaluation_surjective D w)
  refine ⟨C, hC, fun y => ?_⟩
  obtain ⟨x, hx, hn⟩ := h ((originalContinuousLinearEquiv D w).symm y)
  refine ⟨x, (originalContinuousLinearEquiv D w).symm.injective hx, ?_⟩
  simpa only [norm_originalInverse] using hn

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenEvaluationOpen
