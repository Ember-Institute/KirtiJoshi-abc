/-
original-paths: refer/iut/Iut/Concrete/LocalConstruct/Packet.lean,
  refer/iut/Iut/Concrete/LocalConstruct/Archimedean.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commits: Packet 4d2b6e926089b949109c69c28f13c7f878249c5d,
  Archimedean b76207ab8955e68a7408d5d2a770b75a30c3bebf
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: specialize to genuine infinite places; separate the coordinate
  tensor topology from its projective normed model. No LocalTheory, junk
  places, finite-place quotient or reference dependency is retained.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
source-id: JT-SCENE1-LOCAL-ARCHIMEDEAN-TENSOR-INTEGRAL
source: the reference files listed above; IUT IV Proposition 1.5;
Joshi III `th:thetam-construction` and the archimedean tensor factors.
fidelity: for any tuple of actual infinite places, constructs its real/complex
factor models, the real tensor and its projective unit ball B_I. Proves norm
comparison, compactness and a zero neighbourhood. The tensor topology is
Hausdorff by its basis coordinates; no separatedness of the projective
seminorm is assumed. No paper theta-locus or adelic volume identity is assumed.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalArchimedean

open NumberField
open scoped TensorProduct BigOperators

universe u
noncomputable section
variable {K : Type u} [Field K]

open Classical in
def archField (w : InfinitePlace K) : Subalgebra ℝ ℂ :=
  if w.IsReal then ⊥ else ⊤

theorem archField_of_isReal {w : InfinitePlace K} (h : w.IsReal) : archField w = ⊥ := by
  unfold archField
  rw [ite_eq_left h]

theorem archField_of_isComplex {w : InfinitePlace K} (h : w.IsComplex) : archField w = ⊤ := by
  unfold archField
  rw [ite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr h)]

def Factor (w : InfinitePlace K) : Type u := ULift.{u} (archField w)

instance (w : InfinitePlace K) : CommRing (Factor w) :=
  inferInstanceAs (CommRing (ULift (archField w)))
instance (w : InfinitePlace K) : Algebra ℝ (Factor w) :=
  inferInstanceAs (Algebra ℝ (ULift (archField w)))
instance (w : InfinitePlace K) : Module.Finite ℝ (Factor w) :=
  inferInstanceAs (Module.Finite ℝ (ULift (archField w)))
instance (w : InfinitePlace K) : Nontrivial (Factor w) :=
  inferInstanceAs (Nontrivial (ULift (archField w)))

variable {ι : Type} [Fintype ι] (c : ι → InfinitePlace K)

abbrev Tensor : Type u := ⨂[ℝ] j, Factor (c j)
abbrev BasisIndex : Type := ∀ j, Fin (Module.finrank ℝ (Factor (c j)))

instance basisIndexFintype : Fintype (BasisIndex c) := by classical exact inferInstance

instance tensorFinite : Module.Finite ℝ (Tensor c) :=
  inferInstanceAs (Module.Finite ℝ (⨂[ℝ] j, Factor (c j)))

def tensorBasis : Module.Basis (BasisIndex c) ℝ (Tensor c) :=
  Basis.piTensorProduct fun j => Module.finBasis ℝ (Factor (c j))

instance tensorNormedAddCommGroup : NormedAddCommGroup (Tensor c) :=
  NormedAddCommGroup.induced _ (BasisIndex c → ℝ)
    (tensorBasis c).equivFun (tensorBasis c).equivFun.injective
instance tensorNormedSpace : NormedSpace ℝ (Tensor c) :=
  NormedSpace.induced ℝ _ (BasisIndex c → ℝ) (tensorBasis c).equivFun
instance tensorProperSpace : ProperSpace (Tensor c) := FiniteDimensional.proper ℝ _

theorem norm_def (x : Tensor c) : ‖x‖ = ‖(tensorBasis c).equivFun x‖ := rfl

/-- The real/complex factor with its norm, kept separate from the coordinate tensor topology. -/
def NormedFactor (v : InfinitePlace K) : Type u := ULift.{u} (archField v)

noncomputable instance (v : InfinitePlace K) : NormedAddCommGroup (NormedFactor v) :=
  inferInstanceAs (NormedAddCommGroup (ULift (archField v)))

noncomputable instance (v : InfinitePlace K) : NormedSpace ℝ (NormedFactor v) :=
  inferInstanceAs (NormedSpace ℝ (ULift (archField v)))

instance (v : InfinitePlace K) : Module.Finite ℝ (NormedFactor v) :=
  inferInstanceAs (Module.Finite ℝ (ULift (archField v)))

noncomputable instance (v : InfinitePlace K) : One (NormedFactor v) :=
  inferInstanceAs (One (ULift (archField v)))

/-- The archimedean packet presented over the normed factors, carrying Mathlib's projective
seminorm. This type is definitionally `Tensor c`. -/
abbrev ProjectiveModel : Type u := ⨂[ℝ] j, NormedFactor (c j)

/-- The identity map from the packet to its normed model. -/
def toProjectiveModel : Tensor c → ProjectiveModel c := id

/-- **The projective tensor norm** of the archimedean packet. -/
noncomputable def archNorm (x : Tensor c) : ℝ := ‖toProjectiveModel c x‖

/-- **The archimedean integral structure `B_I`**: the closed unit ball of the projective
tensor norm. -/
def archIntegral : Set (Tensor c) := {x | archNorm c x ≤ 1}

lemma mem_archIntegral {x : Tensor c} : x ∈ archIntegral c ↔ archNorm c x ≤ 1 :=
  Iff.rfl

lemma archNorm_nonneg (x : Tensor c) : 0 ≤ archNorm c x := norm_nonneg _

lemma archNorm_add_le (x y : Tensor c) :
    archNorm c (x + y) ≤ archNorm c x + archNorm c y := norm_add_le (E := ProjectiveModel c) _ _

lemma archNorm_smul_le (t : ℝ) (x : Tensor c) :
    archNorm c (t • x) ≤ |t| * archNorm c x := by
  change ‖(t • toProjectiveModel c x : ProjectiveModel c)‖ ≤ |t| * ‖toProjectiveModel c x‖
  rw [← Real.norm_eq_abs]
  exact norm_smul_le t (toProjectiveModel c x)

lemma archNorm_sub_le (x y : Tensor c) :
    |archNorm c x - archNorm c y| ≤ archNorm c (x - y) :=
  abs_norm_sub_norm_le (E := ProjectiveModel c) _ _

lemma archNorm_tprod_le (m : ∀ j, NormedFactor (c j)) :
    archNorm c (PiTensorProduct.tprod ℝ m) ≤ ∏ j, ‖m j‖ :=
  PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℝ) m

lemma archNorm_one : archNorm c 1 ≤ 1 := by
  have h1 : ∀ j, ‖(1 : NormedFactor (c j))‖ = 1 := by
    intro j
    change ‖(1 : ULift.{u} (archField (c j)))‖ = 1
    rw [ULift.norm_def, ULift.one_down]
    change ‖((1 : archField (c j)) : ℂ)‖ = 1
    rw [Subalgebra.coe_one, norm_one]
  have : (1 : Tensor c) = PiTensorProduct.tprod ℝ
      (fun j => (1 : NormedFactor (c j))) := rfl
  rw [this]
  refine (archNorm_tprod_le c _).trans ?_
  simp [h1]

/-- `1 ∈ B_I`. -/
lemma one_mem_archIntegral : (1 : Tensor c) ∈ archIntegral c := archNorm_one c

/-! ### Comparison with the coordinate norm -/

/-- The projective norm is bounded by a multiple of the coordinate norm. -/
lemma exists_archNorm_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Tensor c, archNorm c x ≤ C * ‖x‖ := by
  set b := tensorBasis c
  refine ⟨∑ k, archNorm c (b k), Finset.sum_nonneg fun k _ => archNorm_nonneg c _, fun x => ?_⟩
  conv_lhs => rw [← b.sum_equivFun x]
  calc archNorm c (∑ k, b.equivFun x k • b k)
      ≤ ∑ k, archNorm c (b.equivFun x k • b k) := norm_sum_le (E := ProjectiveModel c) _ _
    _ ≤ ∑ k, ‖x‖ * archNorm c (b k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (archNorm_smul_le c _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (archNorm_nonneg c _)
        rw [← Real.norm_eq_abs, norm_def]
        exact norm_le_pi_norm _ k
    _ = (∑ k, archNorm c (b k)) * ‖x‖ := by rw [Finset.sum_mul]; simp [mul_comm]

/-- The projective norm is continuous. -/
lemma continuous_archNorm : Continuous (archNorm c) := by
  obtain ⟨C, hC0, hC⟩ := exists_archNorm_le c
  refine (LipschitzWith.of_dist_le_mul (K := ⟨C, hC0⟩) fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact (archNorm_sub_le c x y).trans (hC _)

/-- The chosen basis of a factor, as a basis of the normed model of the factor. -/
noncomputable def factorBasis (j : ι) :
    Module.Basis (Fin (Module.finrank ℝ (Factor (c j)))) ℝ
      (NormedFactor (c j)) :=
  (Module.finBasis ℝ (Factor (c j))).map (LinearEquiv.refl ℝ _)

omit [Fintype ι] in
lemma factorBasis_apply (j : ι) (i) :
    factorBasis c j i = Module.finBasis ℝ (Factor (c j)) i := rfl

/-- The coordinate functional of the basis of elementary tensors, as a continuous multilinear
functional on the factors: `a ↦ ∏_j (coordinate `k j` of `a j`)`. -/
noncomputable def coordMultilinear (k : BasisIndex c) :
    ContinuousMultilinearMap ℝ (fun j => NormedFactor (c j)) ℝ where
  toMultilinearMap := (MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap fun j =>
    (factorBasis c j).coord (k j)
  cont := by
    have : ⇑((MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap fun j =>
        (factorBasis c j).coord (k j)) =
        fun m => ∏ j, (factorBasis c j).coord (k j) (m j) := by
      funext m
      rw [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
    change Continuous ⇑((MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap fun j =>
      (factorBasis c j).coord (k j))
    rw [this]
    refine continuous_finsetProd _ fun j _ => ?_
    exact ((factorBasis c j).coord (k j)).continuous_of_finiteDimensional.comp (continuous_apply j)

lemma coordMultilinear_apply (k : BasisIndex c)
    (m : ∀ j, NormedFactor (c j)) :
    (coordMultilinear c k).toMultilinearMap m = ∏ j, (factorBasis c j).coord (k j) (m j) := by
  change ((MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap _) m = _
  rw [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- The lift of `coordMultilinear k` to the packet, as a linear functional on the packet. -/
noncomputable def coordLift (k : BasisIndex c) : Tensor c →ₗ[ℝ] ℝ :=
  PiTensorProduct.lift (coordMultilinear c k).toMultilinearMap

lemma coordLift_apply (k : BasisIndex c) (x : Tensor c) :
    coordLift c k x =
      PiTensorProduct.lift (coordMultilinear c k).toMultilinearMap (toProjectiveModel c x) :=
  rfl

/-- The lift of `coordMultilinear k` to the packet is the `k`-th coordinate functional. -/
lemma coordLift_eq_coord (k : BasisIndex c) :
    coordLift c k = (tensorBasis c).coord k := by
  classical
  refine (tensorBasis c).ext fun l => ?_
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, coordLift_apply]
  have hbl : toProjectiveModel c (tensorBasis c l) =
      PiTensorProduct.tprod ℝ fun j => factorBasis c j (l j) :=
    Basis.piTensorProduct_apply _ l
  rw [hbl, PiTensorProduct.lift.tprod, coordMultilinear_apply]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hl : l = k
  · subst hl
    simp
  · rw [ite_eq_right hl]
    obtain ⟨j, hj⟩ : ∃ j, l j ≠ k j := by
      by_contra h
      push Not at h
      exact hl (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [ite_eq_right hj])

lemma lift_coordMultilinear (k : BasisIndex c) (x : Tensor c) :
    PiTensorProduct.lift (coordMultilinear c k).toMultilinearMap (toProjectiveModel c x) =
      (tensorBasis c).equivFun x k := by
  rw [← coordLift_apply, coordLift_eq_coord, Module.Basis.coord_apply, Module.Basis.equivFun_apply]

/-- The coordinate norm is bounded by a multiple of the projective norm. -/
lemma exists_norm_le_archNorm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Tensor c, ‖x‖ ≤ C * archNorm c x := by
  refine ⟨∑ k, ‖coordMultilinear c k‖, Finset.sum_nonneg fun k _ => norm_nonneg _, fun x => ?_⟩
  rw [norm_def, pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)
    (archNorm_nonneg c x))]
  intro k
  rw [← lift_coordMultilinear]
  calc ‖PiTensorProduct.lift (coordMultilinear c k).toMultilinearMap (toProjectiveModel c x)‖
      ≤ ‖coordMultilinear c k‖ * ‖toProjectiveModel c x‖ :=
        PiTensorProduct.norm_eval_le_projectiveSeminorm _ _
    _ ≤ (∑ k, ‖coordMultilinear c k‖) * archNorm c x :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun k _ => norm_nonneg (coordMultilinear c k)) (Finset.mem_univ k))
          (archNorm_nonneg c x)

/-! ### Properties of `B_I` -/

/-- **`B_I` is closed.** -/
lemma isClosed_archIntegral : IsClosed (archIntegral c) :=
  isClosed_le (continuous_archNorm c) continuous_const

/-- **`B_I` is bounded.** -/
lemma exists_archIntegral_subset_closedBall :
    ∃ M : ℝ, archIntegral c ⊆ Metric.closedBall 0 M := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_archNorm c
  refine ⟨C, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hC x).trans (mul_le_of_le_one_right hC0 hx)

lemma isBounded_archIntegral : Bornology.IsBounded (archIntegral c) := by
  obtain ⟨M, hM⟩ := exists_archIntegral_subset_closedBall c
  exact (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M, hM⟩

/-- **`B_I` is compact.** -/
lemma isCompact_archIntegral : IsCompact (archIntegral c) :=
  (isClosed_archIntegral c).closure_eq ▸ (isBounded_archIntegral c).isCompact_closure

/-- **`B_I` is a neighbourhood of `0`.** -/
lemma exists_ball_subset_archIntegral :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : Tensor c) r ⊆ archIntegral c := by
  obtain ⟨C, hC0, hC⟩ := exists_archNorm_le c
  refine ⟨1 / (C + 1), by positivity, fun x hx => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [mem_archIntegral]
  calc archNorm c x ≤ C * ‖x‖ := hC x
    _ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left hx.le hC0
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith

lemma archIntegral_nonempty : (archIntegral c).Nonempty := ⟨1, one_mem_archIntegral c⟩


end
end JoshiTeich.Act1Scene1.LocalArchimedean
