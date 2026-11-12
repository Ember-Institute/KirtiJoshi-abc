/-
original-paths: `refer/iut/Iut/Concrete/LocalConstruct/Packet.lean`,
  `refer/iut/Iut/Concrete/LocalConstruct/Integral.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commits: Packet `4d2b6e926089b949109c69c28f13c7f878249c5d`,
  Integral `b76207ab8955e68a7408d5d2a770b75a30c3bebf`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: adapted basis-coordinate topology, bounded-span and scaled-basis
openness proofs for actual completion factors and arbitrary positive radii.
No factor quotient, maximal order, hull or tensor volume formula is copied.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensor
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaar
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-LATTICE-TOPOLOGY
fidelity: supplies the finite-dimensional p-adic tensor topology and proves
compact openness of positive-radius integral tensor lattices. The norm is
the norm of basis coordinates, not a claimed tensor cross-norm. No hull or
weighted-volume identification is included.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open NumberField MeasureTheory TopologicalSpace
open scoped TensorProduct BigOperators Pointwise

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

local instance topologyFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance topologyFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance factorContinuousSMul (i : ι) : ContinuousSMul ℚ_[p] (P.Factor i) :=
  continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb (P.residueChar_eq i))
local instance factorModuleTopology (i : ι) : IsModuleTopology ℚ_[p] (P.Factor i) :=
  isModuleTopologyOfFiniteDimensional
local instance topologyIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

abbrev BasisIndex := ∀ i, Fin (Module.finrank ℚ_[p] (P.Factor i))
local instance : Fintype P.BasisIndex := by classical infer_instance

def tensorBasis : Module.Basis P.BasisIndex ℚ_[p] P.Tensor :=
  Basis.piTensorProduct (fun i => Module.finBasis ℚ_[p] (P.Factor i))

instance tensorNormedAddCommGroup : NormedAddCommGroup P.Tensor :=
  NormedAddCommGroup.induced _ (P.BasisIndex → ℚ_[p])
    P.tensorBasis.equivFun P.tensorBasis.equivFun.injective
instance tensorNormedSpace : NormedSpace ℚ_[p] P.Tensor :=
  NormedSpace.induced ℚ_[p] _ (P.BasisIndex → ℚ_[p]) P.tensorBasis.equivFun
instance tensorProperSpace : ProperSpace P.Tensor := FiniteDimensional.proper ℚ_[p] _
instance tensorUltrametric : IsUltrametricDist P.Tensor :=
  ⟨fun x y z => IsUltrametricDist.dist_triangle_max
    (P.tensorBasis.equivFun x) (P.tensorBasis.equivFun y) (P.tensorBasis.equivFun z)⟩

theorem tensor_norm_def (x : P.Tensor) : ‖x‖ = ‖P.tensorBasis.equivFun x‖ := rfl

theorem exists_factor_coordinate_bound (i : ι) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : P.Factor i, ‖a‖ ≤ 1 → ∀ k,
      ‖(Module.finBasis ℚ_[p] (P.Factor i)).repr a k‖ ≤ C := by
  let b := Module.finBasis ℚ_[p] (P.Factor i)
  have hcont : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    ((isCompact_closedBall (0 : P.Factor i) 1).image hcont).isBounded
  refine ⟨max C 0, le_max_right _ _, fun a ha k => ?_⟩
  have h := hC (b.equivFun a) ⟨a, by simpa only [Metric.mem_closedBall, dist_zero_right] using ha, rfl⟩
  exact (norm_le_pi_norm (b.equivFun a) k).trans (h.trans (le_max_left _ _))

theorem unitLattice_isBounded : Bornology.IsBounded (P.unitLattice : Set P.Tensor) := by
  classical
  choose C hC0 hC using P.exists_factor_coordinate_bound
  have hM0 : 0 ≤ ∏ i, C i := Finset.prod_nonneg (fun i _ => hC0 i)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨∏ i, C i, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, rfl⟩ := ht
    rw [tensor_norm_def, pi_norm_le_iff_of_nonneg hM0]
    intro k
    rw [Module.Basis.equivFun_apply, tensorBasis, pure,
      Basis.piTensorProduct_repr_tprod_apply, norm_prod]
    apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
    intro i _
    exact hC i (a i) (by simpa only [Metric.mem_closedBall, dist_zero_right] using ha i) (k i)
  | zero => simpa only [norm_zero] using hM0
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | smul r x _ hx =>
    change ‖(r : ℚ_[p]) • x‖ ≤ _
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one r)).trans hx

theorem exists_pow_smul_factorBasis_mem_ball (i : ι) (r : ℝ) (hr : 0 < r) : ∃ m : ℕ,
    ∀ k, ‖((p : ℚ_[p]) ^ m) • Module.finBasis ℚ_[p] (P.Factor i) k‖ ≤ r := by
  classical
  have hp1 : ‖(p : P.Factor i)‖ < 1 := by
    have h := norm_natCast_prime_lt_one (P.residueChar_eq i)
    rwa [← FinitePlace.embedding_apply, map_natCast] at h
  have hpmap : padicEmb (P.residueChar_eq i) (p : ℚ_[p]) = (p : P.Factor i) := by
    rw [← Rat.cast_natCast, padicEmb_ratCast, Rat.cast_natCast,
      ← FinitePlace.embedding_apply, map_natCast]
  have hm (k : Fin (Module.finrank ℚ_[p] (P.Factor i))) : ∃ m : ℕ,
      ‖(p : P.Factor i)‖ ^ m * ‖Module.finBasis ℚ_[p] (P.Factor i) k‖ ≤ r := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (show 0 < r / (‖Module.finBasis ℚ_[p] (P.Factor i) k‖ + 1) by positivity) hp1
    refine ⟨m, ?_⟩
    calc
      _ ≤ r / (‖Module.finBasis ℚ_[p] (P.Factor i) k‖ + 1) *
          ‖Module.finBasis ℚ_[p] (P.Factor i) k‖ :=
        mul_le_mul_of_nonneg_right hm.le (norm_nonneg _)
      _ ≤ r := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg (Module.finBasis ℚ_[p] (P.Factor i) k)]
  choose m hm using hm
  refine ⟨Finset.univ.sup m, fun k => ?_⟩
  change ‖padicEmb (P.residueChar_eq i) ((p : ℚ_[p]) ^ Finset.univ.sup m) *
    Module.finBasis ℚ_[p] (P.Factor i) k‖ ≤ r
  rw [map_pow, hpmap, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (norm_nonneg _) hp1.le (Finset.le_sup (Finset.mem_univ k)))
    (norm_nonneg _)).trans (hm k)

theorem exists_pow_smul_tensorBasis_mem_lattice (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ M : ℕ, ∀ k : P.BasisIndex,
      (p : ℚ_[p]) ^ M • P.tensorBasis k ∈ P.lattice (fun i => Metric.closedBall 0 (r i)) := by
  classical
  choose m hm using fun i => P.exists_pow_smul_factorBasis_mem_ball i (r i) (hr i)
  refine ⟨∑ i, m i, fun k => ?_⟩
  have h : (p : ℚ_[p]) ^ (∑ i, m i) • P.tensorBasis k =
      P.pure (fun i => (p : ℚ_[p]) ^ m i • Module.finBasis ℚ_[p] (P.Factor i) (k i)) := by
    rw [tensorBasis, Basis.piTensorProduct_apply, ← Finset.prod_pow_eq_pow_sum,
      ← MultilinearMap.map_smul_univ]
    rfl
  rw [h]
  apply P.pure_mem_lattice
  intro i
  simpa only [Metric.mem_closedBall, dist_zero_right] using hm i (k i)

theorem exists_closedBall_subset_lattice (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.closedBall (0 : P.Tensor) ε ⊆
      P.lattice (fun i => Metric.closedBall 0 (r i)) := by
  classical
  obtain ⟨M, hM⟩ := P.exists_pow_smul_tensorBasis_mem_lattice r hr
  have hpM : (p : ℚ_[p]) ^ M ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hp : 0 < ‖(p : ℚ_[p]) ^ M‖ := norm_pos_iff.mpr hpM
  refine ⟨_, hp, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, tensor_norm_def,
    pi_norm_le_iff_of_nonneg hp.le] at hx
  rw [← P.tensorBasis.sum_equivFun x]
  apply Submodule.sum_mem
  intro k _
  have hk : ‖P.tensorBasis.equivFun x k / (p : ℚ_[p]) ^ M‖ ≤ 1 := by
    rw [norm_div, div_le_one hp]
    exact hx k
  let a : ℤ_[p] := ⟨_, hk⟩
  have h : P.tensorBasis.equivFun x k • P.tensorBasis k =
      a • ((p : ℚ_[p]) ^ M • P.tensorBasis k) := by
    change _ = (P.tensorBasis.equivFun x k / (p : ℚ_[p]) ^ M) •
      ((p : ℚ_[p]) ^ M • P.tensorBasis k)
    rw [smul_smul, div_mul_cancel₀ _ hpM]
  rw [h]
  exact Submodule.smul_mem _ a (hM k)

theorem lattice_balls_isOpen (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    IsOpen (P.lattice (fun i => Metric.closedBall 0 (r i)) : Set P.Tensor) := by
  obtain ⟨ε, hε, hsub⟩ := P.exists_closedBall_subset_lattice r hr
  exact AddSubgroup.isOpen_of_mem_nhds
    (P.lattice (fun i => Metric.closedBall 0 (r i))).toAddSubgroup
    (Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : P.Tensor) hε) hsub)

theorem lattice_balls_isCompact (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hr1 : ∀ i, r i ≤ 1) :
    IsCompact (P.lattice (fun i => Metric.closedBall 0 (r i)) : Set P.Tensor) := by
  have hclosed := AddSubgroup.isClosed_of_isOpen
    (P.lattice (fun i => Metric.closedBall 0 (r i))).toAddSubgroup (P.lattice_balls_isOpen r hr)
  have hbound := P.unitLattice_isBounded.subset
    (P.lattice_mono (fun i => Metric.closedBall_subset_closedBall (hr1 i)))
  exact hclosed.closure_eq ▸ hbound.isCompact_closure

/-- Haar measure on the actual finite-dimensional tensor topology. -/
instance tensorMeasurableSpace : MeasurableSpace P.Tensor := borel _
instance tensorBorelSpace : BorelSpace P.Tensor := ⟨rfl⟩
def haar : Measure P.Tensor := Measure.addHaar
instance haar_isAddHaarMeasure : P.haar.IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaar : Measure P.Tensor).IsAddHaarMeasure

theorem lattice_balls_haar_pos_lt_top (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hr1 : ∀ i, r i ≤ 1) :
    0 < P.haar (P.lattice (fun i => Metric.closedBall 0 (r i))) ∧
      P.haar (P.lattice (fun i => Metric.closedBall 0 (r i))) < ⊤ := by
  exact ⟨(P.lattice_balls_isOpen r hr).measure_pos _ ⟨0, Submodule.zero_mem _⟩,
    (P.lattice_balls_isCompact r hr hr1).measure_lt_top⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
