/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/Hull.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: fe96f99cae5c6d48d25113163f1b9b388fc35814
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt bounded-region residue norm estimates to actual Packet,
using its existing normalization neighborhood and spectral unit-ball criterion.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueBallRegions
import Mathlib.Tactic.Linarith

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-BOUNDED-RESIDUES
fidelity: bounds all residue spectral norms uniformly on any actual tensor
bounded set. It uses scalar contraction into the actual normalization;
no comparison of quotient and spectral topologies is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance boundsFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance boundsFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)

theorem exists_closedBall_subset_normalization :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : P.Tensor) r ⊆ P.normalization := by
  obtain ⟨r, hr, hsub⟩ := P.exists_closedBall_subset_lattice (fun _ => 1) (fun _ => zero_lt_one)
  exact ⟨r, hr, hsub.trans P.unitLattice_le_normalization⟩

theorem exists_uniform_residueNorm_bound {U : Set P.Tensor} (hU : Bornology.IsBounded U) :
    ∃ B : ℝ, ∀ x ∈ U, ∀ I : MaximalSpectrum P.Tensor,
      P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) ≤ B := by
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  obtain ⟨r, hr, hsub⟩ := P.exists_closedBall_subset_normalization
  have hp1 : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hp0 : 0 < ‖(p : ℚ_[p])‖ :=
    norm_pos_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < r / (|R| + 1) by positivity) hp1
  let q : ℚ_[p] := (p : ℚ_[p]) ^ n
  have hq0 : 0 < ‖q‖ := by dsimp [q]; rw [norm_pow]; exact pow_pos hp0 n
  refine ⟨‖q‖⁻¹, fun x hx I => ?_⟩
  have hxR : ‖x‖ ≤ |R| + 1 := by
    have h := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h.trans ((le_abs_self R).trans (by linarith))
  have hmem : q • x ∈ P.normalization := by
    apply hsub
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    change ‖(p : ℚ_[p]) ^ n‖ * ‖x‖ ≤ r
    rw [norm_pow]
    calc
      _ ≤ r / (|R| + 1) * (|R| + 1) := mul_le_mul hn.le hxR (norm_nonneg _) (by positivity)
      _ = r := div_mul_cancel₀ r (by positivity)
  have h := (P.mem_normalization_iff_residueNorm_le_one (q • x)).mp hmem I
  have hmap : Ideal.Quotient.mk I.asIdeal (q • x) =
      algebraMap ℚ_[p] (P.Tensor ⧸ I.asIdeal) q * Ideal.Quotient.mk I.asIdeal x := by
    rw [Algebra.smul_def, map_mul]
    rfl
  rw [hmap, P.residueNorm_mul, P.residueNorm_algebraMap] at h
  calc
    P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) =
        ‖q‖⁻¹ * (‖q‖ * P.residueNorm I (Ideal.Quotient.mk I.asIdeal x)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hq0.ne', one_mul]
    _ ≤ ‖q‖⁻¹ * 1 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hq0.le)
    _ = ‖q‖⁻¹ := mul_one _

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
