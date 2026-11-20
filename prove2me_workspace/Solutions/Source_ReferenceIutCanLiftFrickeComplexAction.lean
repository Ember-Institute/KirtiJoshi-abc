/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as stated in the upstream source headers.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/M2/Final.lean and OrbicurveCores/M2/Unipotent.lean
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Solutions.Source_ReferenceIutCanLiftFrickeNormalForm
import Solutions.Source_ReferenceIutCanLiftThreePoint

set_option autoImplicit false

/-!
# Complex projective action of the Fricke normal form

The commutator acts by translation by two under every ring embedding of `ℝ` into `ℂ`.
Its powers send the standard triple to a sequence that converges to `(∞, ∞, ∞)`.
-/

open Filter OnePoint OnePoint.Proj Topology
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke (nA nB coe_commutator_n)

variable {k : Type*} [Field k]

/-- Apply a ring homomorphism to the entries of a real special linear matrix. -/
noncomputable def slMap (σ : ℝ →+* k) : SL(2, ℝ) →* GL (Fin 2) k :=
  (Matrix.GeneralLinearGroup.map σ).comp Matrix.SpecialLinearGroup.toGL

lemma coe_slMap (σ : ℝ →+* k) (g : SL(2, ℝ)) :
    (slMap σ g : Matrix (Fin 2) (Fin 2) k) = (g : Matrix (Fin 2) (Fin 2) ℝ).map σ := rfl

lemma slMap_mul (σ : ℝ →+* k) (g h : SL(2, ℝ)) :
    slMap σ (g * h) = slMap σ g * slMap σ h := (slMap σ).map_mul g h

/-- The projective translation by `b`. -/
def transl (b : k) : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, b; 0, 1] (by simp [Matrix.det_fin_two])

variable [DecidableEq k]

lemma transl_smul_coe (b a : k) : transl b • (a : OnePoint k) = ((a + b : k) : OnePoint k) := by
  rw [smul_some_eq_ite]
  simp [transl, add_comm]

lemma transl_smul_infty (b : k) : transl b • (∞ : OnePoint k) = ∞ := by
  rw [smul_infty_eq_self_iff]
  simp [transl]

lemma transl_iterate (b : k) (n : ℕ) (w : OnePoint k) :
    (fun a ↦ transl b • a)^[n] w = transl (n * b) • w := by
  induction n generalizing w with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_mul]
    cases w with
    | infty => rw [transl_smul_infty]
    | coe a => rw [transl_smul_coe, add_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    cases w with
    | infty => simp only [transl_smul_infty]
    | coe a =>
      simp only [transl_smul_coe, OnePoint.coe_eq_coe, Nat.cast_succ]
      ring

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The commutator of the normal-form generators. -/
noncomputable def commK : SL(2, ℝ) := nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹

lemma commK_mem : commK hz hrel ∈ Subgroup.closure {nA hz hrel, nB hz hrel} := by
  have hA : nA hz hrel ∈ Subgroup.closure {nA hz hrel, nB hz hrel} :=
    Subgroup.subset_closure (by simp)
  have hB : nB hz hrel ∈ Subgroup.closure {nA hz hrel, nB hz hrel} :=
    Subgroup.subset_closure (by simp)
  exact mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)

lemma coe_commK : (commK hz hrel : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, -2; 0, -1] :=
  coe_commutator_n hz hrel

lemma slMap_commK (σ : ℝ →+* k) (w : OnePoint k) :
    slMap σ (commK hz hrel) • w = transl (2 : k) • w := by
  rw [gl_smul_eq_mob, gl_smul_eq_mob, coe_slMap, coe_commK]
  have hmatrix : (!![-1, -2; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).map σ =
      (-1 : k) • (transl (2 : k) : Matrix (Fin 2) (Fin 2) k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transl, map_ofNat]
  rw [hmatrix, mob_smul_matrix (neg_ne_zero.mpr one_ne_zero)]

private lemma tendsto_coe_infty_of_norm {f : ℕ → ℂ} (hf : Tendsto (fun n ↦ ‖f n‖) atTop atTop) :
    Tendsto (fun n ↦ (f n : OnePoint ℂ)) atTop (𝓝 ∞) := by
  intro U hU
  obtain ⟨R, -, hR⟩ := exists_norm_ge_mem hU
  exact (hf.eventually_ge_atTop R).mono fun n hn ↦ hR _ hn

/-- The embedded normal-form group sends `(0, 1, ∞)` towards a degenerate triple. -/
theorem unbounded_complex [DecidableEq ℂ] (σ : ℝ →+* ℂ) :
    ∃ γs : ℕ → SL(2, ℝ), (∀ n, γs n ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) ∧
      ∃ τ : Triple ℂ, ¬ Distinct3 τ ∧
        Tendsto (fun n ↦ smul3 (slMap σ (γs n)) e₃) atTop (𝓝 τ) := by
  refine ⟨fun n ↦ commK hz hrel ^ n, fun n ↦ pow_mem (commK_mem hz hrel) n, (∞, ∞, ∞),
    fun h ↦ h.1 rfl, ?_⟩
  have hpow (n : ℕ) (w : OnePoint ℂ) :
      slMap σ (commK hz hrel ^ n) • w = transl ((n : ℂ) * 2) • w := by
    rw [map_pow, ← smul_iterate_apply,
      show (fun a : OnePoint ℂ ↦ slMap σ (commK hz hrel) • a) = (fun a ↦ transl (2 : ℂ) • a)
        from funext (slMap_commK hz hrel σ), transl_iterate]
  have hnorm (c : ℂ) : Tendsto (fun n : ℕ ↦ ‖c + (n : ℂ) * 2‖) atTop atTop := by
    refine tendsto_atTop_mono (fun n ↦ ?_) (tendsto_atTop_add_const_right _ (-‖c‖)
      (tendsto_natCast_atTop_atTop.atTop_mul_const (show (0 : ℝ) < 2 by norm_num)))
    calc
      (n : ℝ) * 2 + -‖c‖ = ‖(n : ℂ) * 2‖ - ‖c‖ := by
        rw [Complex.norm_mul, Complex.norm_natCast, Complex.norm_two, sub_eq_add_neg]
      _ ≤ ‖c + (n : ℂ) * 2‖ := by
        simpa only [norm_neg, sub_neg_eq_add, add_comm] using norm_sub_norm_le ((n : ℂ) * 2) (-c)
  simp only [smul3, e₃, hpow, transl_smul_coe, transl_smul_infty]
  exact (tendsto_coe_infty_of_norm (hnorm 0)).prodMk_nhds
    ((tendsto_coe_infty_of_norm (hnorm 1)).prodMk_nhds tendsto_const_nhds)

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
