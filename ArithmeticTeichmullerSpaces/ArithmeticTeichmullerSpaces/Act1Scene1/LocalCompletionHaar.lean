/-
original-paths: `refer/iut/Iut/Concrete/LocalConstruct/Integral.lean`,
  `refer/iut/Iut/Concrete/LocalConstruct/LogShell.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commits: Integral `b76207ab8955e68a7408d5d2a770b75a30c3bebf`,
  LogShell `fe96f99cae5c6d48d25113163f1b9b388fc35814`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: selected completion compactness and properness proofs;
independent namespace and exact imports. New Haar normalization and scalar
measure proofs use Mathlib; no tensor-packet construction is copied.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionPadicAlgebra
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-HAAR
fidelity: derives properness of actual completions and constructs an
additive Haar measure normalized on the integral unit ball. Scalar-ball
measure is expressed by the actual Haar character; its identification
with the chosen completion norm remains a separate proof obligation.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace
open JoshiTeich.Prologue.Arithmetic
open scoped Pointwise

universe u
variable {K : Type u} [Field K] [NumberField K]

section Compact
variable {p : ℕ} [Fact p.Prime] {w : FinitePlace K} (hw : residueChar w = p)
include hw

/-- **The ring of integers `𝓞_w` of a completion is relatively compact in the
`ℚ_p`-coordinates**: it is contained in a compact subset of `K_w`. -/
theorem exists_isCompact_closedBall_subset :
    ∃ C : Set (completionAt K w), IsCompact C ∧ Metric.closedBall (0 : completionAt K w) 1 ⊆ C := by
  letI := padicAlgebra hw
  haveI : ContinuousSMul ℚ_[p] (completionAt K w) :=
    continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb hw)
  haveI := finite_padicAlgebra hw
  haveI : IsModuleTopology ℚ_[p] (completionAt K w) := isModuleTopologyOfFiniteDimensional
  let b := Module.finBasis ℚ K
  let φ : (Fin (Module.finrank ℚ K) → ℚ_[p]) →ₗ[ℚ_[p]] completionAt K w :=
    Fintype.linearCombination ℚ_[p] fun i => ((b i : K) : completionAt K w)
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact span_range_finBasis_eq_top hw
  set B : Set (Fin (Module.finrank ℚ K) → ℚ_[p]) := Set.pi Set.univ fun _ => Metric.closedBall 0 1
    with hB
  have hBopen : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBcompact : IsCompact B := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hΛopen : IsOpen (φ '' B) := IsModuleTopology.isOpenMap_of_surjective hφ _ hBopen
  have hΛcompact : IsCompact (φ '' B) :=
    hBcompact.image (IsModuleTopology.continuous_of_linearMap φ)
  have h0 : φ '' B ∈ nhds (0 : completionAt K w) :=
    hΛopen.mem_nhds ⟨0, fun _ _ => by simp, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h0
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime_lt_one hw)
  have hp0 : ((p : K) : completionAt K w) ≠ 0 := by
    have : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact (map_ne_zero_iff _ (FinitePlace.embedding w.maximalIdeal).injective).mpr this
  refine ⟨(fun y => (((p : K) : completionAt K w) ^ r)⁻¹ * y) '' (φ '' B),
    hΛcompact.image (by fun_prop), fun x hx => ?_⟩
  refine ⟨((p : K) : completionAt K w) ^ r * x, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
    calc ‖((p : K) : completionAt K w)‖ ^ r * ‖x‖
        ≤ ‖((p : K) : completionAt K w)‖ ^ r * 1 :=
          mul_le_mul_of_nonneg_left (by simpa using hx) (by positivity)
      _ < ε := by simpa using hr
  · dsimp only
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]

end Compact

/-- **The completions of a number field are proper spaces**: closed balls are compact (they
are contained in a rescaling of the compact set of `exists_isCompact_closedBall_subset`). -/
instance instProperSpaceCompletionAt (w : FinitePlace K) : ProperSpace (completionAt K w) := by
  haveI : Fact (residueChar w).Prime := ⟨residueChar_prime w⟩
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_closedBall_subset (p := residueChar w) (w := w) rfl
  have hp1 := norm_natCast_prime_lt_one (p := residueChar w) (w := w) rfl
  have hp0 : (((residueChar w : ℕ) : K) : completionAt K w) ≠ 0 := by
    have : ((residueChar w : ℕ) : K) ≠ 0 := by exact_mod_cast (residueChar_prime w).ne_zero
    exact (map_ne_zero_iff _ (FinitePlace.embedding w.maximalIdeal).injective).mpr this
  refine ProperSpace.of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  -- `closedBall x r ⊆ x + p^{-m} • C` for `‖p‖^m r ≤ 1`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖(((residueChar w : ℕ) : K) : completionAt K w)‖ ^ m * r ≤ 1 := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (r + 1) by positivity) hp1
    refine ⟨m, ?_⟩
    calc ‖(((residueChar w : ℕ) : K) : completionAt K w)‖ ^ m * r
        ≤ 1 / (r + 1) * r := mul_le_mul_of_nonneg_right hm.le hr
      _ ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        linarith
  set q : completionAt K w := (((residueChar w : ℕ) : K) : completionAt K w) ^ m with hq
  have hq0 : q ≠ 0 := pow_ne_zero _ hp0
  have hcpt : IsCompact ((fun y => x + q⁻¹ * y) '' C) := hC.image (by fun_prop)
  refine hcpt.of_isClosed_subset Metric.isClosed_closedBall fun y hy => ?_
  refine ⟨q * (y - x), hsub ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, hq, norm_pow]
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    calc ‖(((residueChar w : ℕ) : K) : completionAt K w)‖ ^ m * ‖y - x‖
        ≤ ‖(((residueChar w : ℕ) : K) : completionAt K w)‖ ^ m * r :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ ≤ 1 := hm
  · dsimp only
    rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul, add_sub_cancel]


/-- The integral unit ball is a compact set with nonempty interior. -/
noncomputable def integralUnitBall (w : FinitePlace K) : PositiveCompacts (completionAt K w) where
  carrier := Metric.closedBall 0 1
  isCompact' := isCompact_closedBall _ _
  interior_nonempty' := by
    rw [(IsUltrametricDist.isOpen_closedBall (0 : completionAt K w) one_ne_zero).interior_eq]
    exact ⟨0, by simp⟩

noncomputable instance instMeasurableCompletion (w : FinitePlace K) :
    MeasurableSpace (completionAt K w) := borel _

instance instBorelCompletion (w : FinitePlace K) : BorelSpace (completionAt K w) := ⟨rfl⟩

/- The actual Haar measure with integral unit ball measure one. -/
noncomputable def normalizedHaar (w : FinitePlace K) : Measure (completionAt K w) :=
  Measure.addHaarMeasure (integralUnitBall w)

section Haar
variable (w : FinitePlace K)

noncomputable instance normalizedHaar_isAddHaarMeasure : (normalizedHaar w).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaarMeasure (integralUnitBall w)).IsAddHaarMeasure

noncomputable instance normalizedHaar_regular : (normalizedHaar w).Regular :=
  inferInstanceAs (Measure.addHaarMeasure (integralUnitBall w)).Regular

theorem normalizedHaar_unitBall : normalizedHaar w (Metric.closedBall 0 1) = 1 :=
  Measure.addHaarMeasure_self

/-- Haar scaling on a scalar integral ball uses the measure's distributive character. -/
theorem normalizedHaar_scalarBall (z : completionAt K w) (hz : z ≠ 0) :
    normalizedHaar w ((fun x => z * x) '' Metric.closedBall 0 1) =
      (distribHaarChar (completionAt K w) (Units.mk0 z hz) : ENNReal) := by
  have h := distribHaarChar_mul (normalizedHaar w) (Units.mk0 z hz)
    (Metric.closedBall (0 : completionAt K w) 1)
  rw [normalizedHaar_unitBall, mul_one] at h
  exact h.symm

end Haar
end JoshiTeich.Act1Scene1.LocalCompletion
