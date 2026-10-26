import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalTateSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaPadicQuotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RATIONAL-TATE-PERIOD
source: Joshi II `pr:teichmuller-lift-A`, the T_y tensor Q_p arrow
into the actual phi=p space and the canonical evaluation kernel.
fidelity: constructs a continuous Q_p-linear map from the actual Tate
tensor rationalization. On every pure tensor it is scalar times the
original convergent Tate logarithm. Proves injectivity, closed embedding,
and that its image is the one-dimensional span of the actual canonical
Tate period, contained in both the phi=p space and the same theta kernel.
Restricts to the actual phi=p space, with a closed embedding and zero
composition with its actual continuous evaluation.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; equality with the full phi=p evaluation kernel
and surjectivity of its evaluation remain separate obligations. The
original period-ring topology and Prologue R5 are unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRationalTatePeriod

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittTateLogarithm InitialThetaWittRationalTateSource
open InitialThetaWittAdditiveTatePeriod
open scoped TensorProduct Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def periodMap : RationalTate D w →L[Padic (Arithmetic.residueChar w.1)] Carrier D w :=
  (ContinuousLinearMap.toSpanSingleton (Padic (Arithmetic.residueChar w.1))
    (tateLog D w (InitialThetaCyclotomicTateTilt.generator D w))).comp
      (coefficientIsometryEquiv D w).toContinuousLinearEquiv.toContinuousLinearMap

theorem periodMap_apply (x : RationalTate D w) :
    periodMap D w x = coefficientEquiv D w x •
      tateLog D w (InitialThetaCyclotomicTateTilt.generator D w) := rfl

theorem periodMap_tmul (a : Padic (Arithmetic.residueChar w.1)) (t : Additive (Tate D w)) :
    periodMap D w (a ⊗ₜ t) = a • tateLog D w t.toMul := by
  rw [periodMap_apply, coefficientEquiv_tmul, mul_smul]
  have ht := InitialThetaWittTateLogarithmLinear.tateLogHom_basis_formula D w t
  change tateLog D w t.toMul = ((integralBasis D w).symm t : Padic (Arithmetic.residueChar w.1)) •
    tateLog D w (InitialThetaCyclotomicTateTilt.generator D w) at ht
  rw [← ht]

theorem periodMap_one_tmul (t : Additive (Tate D w)) :
    periodMap D w ((1 : Padic (Arithmetic.residueChar w.1)) ⊗ₜ t) = tateLog D w t.toMul := by
  rw [periodMap_tmul, one_smul]

theorem periodMap_injective : Function.Injective (periodMap D w) := by
  intro x y h
  apply (coefficientEquiv D w).injective
  apply smul_left_injective (Padic (Arithmetic.residueChar w.1))
    (InitialThetaWittTateLogarithmInjective.canonical_tateLog_ne_zero D w)
  exact h

theorem periodMap_isClosedEmbedding : Topology.IsClosedEmbedding (periodMap D w) :=
  LinearMap.isClosedEmbedding_of_injective (f := (periodMap D w).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (periodMap_injective D w))

theorem periodMap_range : (periodMap D w).range =
    Submodule.span (Padic (Arithmetic.residueChar w.1))
      {tateLog D w (InitialThetaCyclotomicTateTilt.generator D w)} := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change periodMap D w v ∈ _
    rw [periodMap_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨(coefficientEquiv D w).symm a, ?_⟩
    change periodMap D w ((coefficientEquiv D w).symm a) = x
    rw [periodMap_apply, LinearEquiv.apply_symm_apply]
    exact ha

theorem periodMap_range_isClosed : IsClosed ((periodMap D w).range : Set (Carrier D w)) :=
  (periodMap_isClosedEmbedding D w).isClosed_range

theorem periodMap_range_finrank : Module.finrank (Padic (Arithmetic.residueChar w.1))
    (periodMap D w).range = 1 :=
  (LinearMap.finrank_range_of_inj (f := (periodMap D w).toLinearMap) (periodMap_injective D w)).trans
    (rationalTate_finrank D w)

theorem periodMap_range_le_frobeniusPrime : (periodMap D w).range ≤ frobeniusPrimeSubmodule D w := by
  rintro x ⟨v, rfl⟩
  change periodMap D w v ∈ _
  rw [periodMap_apply]
  exact (frobeniusPrimeSubmodule D w).smul_mem _ (tateLog_mem_frobeniusPrime D w _)

theorem periodMap_range_le_kernel : (periodMap D w).range ≤
    InitialThetaWittThetaPadicQuotient.kernelSubmodule D w := by
  rintro x ⟨v, rfl⟩
  change periodMap D w v ∈ _
  rw [periodMap_apply]
  exact (InitialThetaWittThetaPadicQuotient.kernelSubmodule D w).smul_mem _
    (InitialThetaWittThetaPadicQuotient.tateLog_mem_kernelSubmodule D w _)

def eigenPeriodMap : RationalTate D w →L[Padic (Arithmetic.residueChar w.1)]
    frobeniusPrimeSubmodule D w :=
  (periodMap D w).codRestrict (frobeniusPrimeSubmodule D w)
    (fun x => periodMap_range_le_frobeniusPrime D w ⟨x, rfl⟩)

theorem eigenPeriodMap_tmul (a : Padic (Arithmetic.residueChar w.1)) (t : Additive (Tate D w)) :
    (eigenPeriodMap D w (a ⊗ₜ t) : Carrier D w) = a • tateLog D w t.toMul :=
  periodMap_tmul D w a t

theorem eigenPeriodMap_injective : Function.Injective (eigenPeriodMap D w) := by
  intro x y h
  exact periodMap_injective D w (congrArg Subtype.val h)

theorem eigenPeriodMap_isClosedEmbedding : Topology.IsClosedEmbedding (eigenPeriodMap D w) :=
  LinearMap.isClosedEmbedding_of_injective (f := (eigenPeriodMap D w).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (eigenPeriodMap_injective D w))

def eigenEvaluation : frobeniusPrimeSubmodule D w →L[Padic (Arithmetic.residueChar w.1)]
    InitialThetaWittThetaBound.Untilt D w :=
  (InitialThetaWittThetaPadicCompatibility.evaluationContinuousLinear D w).domRestrict
    (frobeniusPrimeSubmodule D w)

theorem eigenEvaluation_comp_periodMap : (eigenEvaluation D w).comp (eigenPeriodMap D w) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change InitialThetaWittThetaEvaluation.evaluation D w (periodMap D w x) = 0
  exact (InitialThetaWittThetaPadicQuotient.mem_kernelSubmodule D w _).mp
    (periodMap_range_le_kernel D w ⟨x, rfl⟩)

end
end JoshiTeich.Act1Scene1.InitialThetaWittRationalTatePeriod
