/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Unipotent.lean
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FunProp
import Solutions.Source_ReferenceIutCanLiftUnipotent

set_option autoImplicit false

open Set Topology OnePoint OnePoint.Proj
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

section complex

open UnipotentRigidity

variable [DecidableEq ℂ]

/-- Upper and lower unipotent matrices over `ℂ`. -/
def TU (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, t; 0, 1]
def TL (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; s, 1]

omit [DecidableEq ℂ] in
lemma det_TU (t : ℂ) : (TU t).det = 1 := by simp [TU, Matrix.det_fin_two]
omit [DecidableEq ℂ] in
lemma det_TL (s : ℂ) : (TL s).det = 1 := by simp [TL, Matrix.det_fin_two]

omit [DecidableEq ℂ] in
lemma conj_TU {G : Matrix (Fin 2) (Fin 2) ℂ} (hG10 : G 1 0 ≠ 0)
    (hdetG : G 0 0 * G 1 1 - G 0 1 * G 1 0 = 1) (t : ℂ) :
    G * TU t * G.adjugate =
      TU (G 0 0 / G 1 0) * TL (-(G 1 0) ^ 2 * t) * TU (-(G 0 0 / G 1 0)) := by
  rw [Matrix.eta_fin_two G, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [TU, TL]; field_simp; linear_combination hdetG
  · simp [TU, TL]; field_simp; ring
  · simp [TU, TL]; ring
  · simp [TU, TL]; field_simp; linear_combination hdetG

lemma transl_smul_eq_mob (b : ℂ) (y : OnePoint ℂ) : transl b • y = OnePoint.Proj.mob (TU b) y := by
  rw [gl_smul_eq_mob]; rfl

set_option linter.flexible false in
lemma continuous_transl_smul (y : OnePoint ℂ) : Continuous fun t : ℝ ↦ transl (t : ℂ) • y := by
  simp_rw [transl_smul_eq_mob]
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have hM : Continuous fun t : ℝ ↦ TU (t : ℂ) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp only [TU] <;> simp <;> fun_prop
  exact (continuousAt_mob_param hM.continuousAt (by rw [det_TU]; exact one_ne_zero) y).comp
    (f := fun t : ℝ ↦ (t, y)) (by fun_prop)

variable {Φ : SL(2, ℝ) → GL (Fin 2) ℂ}
  (hΦ : ∀ g h : SL(2, ℝ), ∀ y : OnePoint ℂ, Φ (g * h) • y = Φ g • Φ h • y)
  (hcont : ∀ y : OnePoint ℂ, Continuous fun g ↦ Φ g • y) (h2 : IsTransl Φ 2 2)
include hΦ hcont h2

/-- Over `ℂ`, `Φ(u_t)` is translation by `t` for every real `t`. -/
theorem smul_uU_real (t : ℝ) (y : OnePoint ℂ) : Φ (SL2R.uU t) • y = transl (t : ℂ) • y := by
  have h1 : Continuous fun t : ℝ ↦ Φ (SL2R.uU t) • y := (hcont y).comp SL2R.continuous_uU
  have h2' : Continuous fun t : ℝ ↦ transl (t : ℂ) • y := continuous_transl_smul y
  have := h1.ext_on Rat.denseRange_cast h2' (by
    rintro _ ⟨q, rfl⟩
    have := smul_uU_rat hΦ h2 q y
    simpa using this)
  exact congrFun this t

omit hcont h2 in
lemma smul_inv_of_mob {γ : SL(2, ℝ)} {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.det ≠ 0)
    (hγ : ∀ y, Φ γ • y = OnePoint.Proj.mob G y) (y : OnePoint ℂ) :
    Φ γ⁻¹ • y = OnePoint.Proj.mob G.adjugate y := by
  have e : Φ γ⁻¹ • Φ γ • (OnePoint.Proj.mob G.adjugate y) = OnePoint.Proj.mob G.adjugate y := by
    rw [← hΦ, inv_mul_cancel, smul_one' hΦ]
  rwa [hγ, mob_mul_adjugate hG] at e

set_option linter.flexible false in
/-- **Complex rigidity.** If `Φ` is a continuous extension over `ℂ` of an action that agrees
with `σ` (an arbitrary ring embedding `ℝ → ℂ`) on some `γ` with `γ₁₀ ≠ 0`, and `Φ(-1) = 1`,
then `σ(γ₁₀)² = γ₁₀²`. -/
theorem complex_rigidity (hneg : ∀ y : OnePoint ℂ, Φ (-1) • y = y) (σ : ℝ →+* ℂ)
    {γ : SL(2, ℝ)}
    (hγ : ∀ y, Φ γ • y = OnePoint.Proj.mob ((γ : Matrix (Fin 2) (Fin 2) ℝ).map σ) y)
    (hr : γ 1 0 ≠ 0) : σ (γ 1 0) ^ 2 = ((γ 1 0 : ℝ) : ℂ) ^ 2 := by
  set r := γ 1 0
  set ξ := γ 0 0 / r
  set G : Matrix (Fin 2) (Fin 2) ℂ := (γ : Matrix (Fin 2) (Fin 2) ℝ).map σ
  have hdetγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hG : G.det = 1 := by
    change (σ.mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℝ)).det = 1
    rw [← RingHom.map_det, γ.2, map_one]
  have hGne : G.det ≠ 0 := by rw [hG]; exact one_ne_zero
  have hσr : σ r ≠ 0 := by
    intro h; apply hr; exact σ.injective (by rw [h, map_zero])
  -- `u_L(-1) = u(-ξ) γ u(1/r²) γ⁻¹ u(ξ)`
  have hid : SL2R.uL (-1) = SL2R.uU (-ξ) * γ * SL2R.uU (1 / r ^ 2) * γ⁻¹ * SL2R.uU ξ := by
    have hξ : ξ * r = γ 0 0 := div_mul_cancel₀ _ hr
    have hdetξ : ξ * r * γ 1 1 - γ 0 1 * r = 1 := by
      rw [hξ]
      exact hdetγ
    have ht : r ^ 2 * (1 / r ^ 2) = 1 := by
      rw [one_div, mul_inv_cancel₀ (pow_ne_zero 2 hr)]
    have hm : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![ξ * r, γ 0 1; r, γ 1 1] := by
      rw [hξ]
      exact Matrix.eta_fin_two _
    apply Subtype.ext
    change (↑(SL2R.uL (-1)) : Matrix (Fin 2) (Fin 2) ℝ) =
      ↑(SL2R.uU (-ξ) * γ * SL2R.uU (1 / r ^ 2) * γ⁻¹ * SL2R.uU ξ)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      SL2R.coe_uL, SL2R.coe_uU]
    rw [hm, Matrix.adjugate_fin_two_of]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
      linear_combination -hdetξ
    · simp <;> ring
    · simp
      linear_combination ht
    · simp
      linear_combination -hdetξ
  -- matrix identities over `ℂ`
  have hTU : ∀ a b : ℂ, TU a * TU b = TU (a + b) := by
    intro a b; ext i j; fin_cases i <;> fin_cases j <;> simp [TU]; ring
  have hconj : ∀ t : ℂ, G * TU t * G.adjugate =
      TU (G 0 0 / G 1 0) * TL (-(G 1 0) ^ 2 * t) * TU (-(G 0 0 / G 1 0)) := fun t ↦
    conj_TU (by simpa [G] using hσr) (by rw [← Matrix.det_fin_two]; exact hG) t
  have hG10 : G 1 0 = σ r := rfl
  have hG00 : G 0 0 = σ (γ 0 0) := rfl
  set d : ℂ := G 0 0 / G 1 0 - (ξ : ℂ)
  set b : ℂ := -(G 1 0) ^ 2 * ((1 / r ^ 2 : ℝ) : ℂ)
  have hTUdet : ∀ a : ℂ, (TU a).det ≠ 0 := fun a ↦ by rw [det_TU]; exact one_ne_zero
  have hTLdet : ∀ a : ℂ, (TL a).det ≠ 0 := fun a ↦ by rw [det_TL]; exact one_ne_zero
  have hadj : G.adjugate.det ≠ 0 := by rw [Matrix.det_adjugate]; simpa using hGne
  have hU : ∀ (t : ℝ) (y : OnePoint ℂ), Φ (SL2R.uU t) • y = OnePoint.Proj.mob (TU t) y :=
    fun t y ↦ by rw [smul_uU_real hΦ hcont h2, transl_smul_eq_mob]
  -- `Φ(u_L(-1))`
  obtain ⟨M₁, hM₁def⟩ : ∃ M, M = TU (-(ξ : ℂ)) * G * TU ((1 / r ^ 2 : ℝ) : ℂ) * G.adjugate *
      TU (ξ : ℂ) := ⟨_, rfl⟩
  have hL : ∀ y, Φ (SL2R.uL (-1)) • y = OnePoint.Proj.mob M₁ y := by
    intro y
    rw [hid, hΦ, hΦ, hΦ, hΦ, hU, hγ, hU, smul_inv_of_mob hΦ hGne hγ, hU, hM₁def]
    rw [mob_mul (hTUdet _), mob_mul hadj, mob_mul (hTUdet _), mob_mul hGne]
    push_cast
    rfl
  have hM₁ : M₁ = TU d * TL b * TU (-d) := by
    simp only [hM₁def, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc (G * TU _), hconj]
    simp only [← Matrix.mul_assoc, hTU]
    simp only [Matrix.mul_assoc, hTU]
    simp only [d, b]
    congr 2 <;> ring
  -- the Weyl element
  set W := SL2R.uU 1 * SL2R.uL (-1) * SL2R.uU 1
  have hW : W * W = -1 := by
    apply Subtype.ext
    change (↑(W * W) : Matrix (Fin 2) (Fin 2) ℝ) = ↑(-1 : SL(2, ℝ))
    simp only [W, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, SL2R.coe_uU, SL2R.coe_uL, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hM1det : M₁.det ≠ 0 := by
    rw [hM₁, Matrix.det_mul, Matrix.det_mul, det_TU, det_TL, det_TU]; norm_num
  obtain ⟨N, hNdef⟩ : ∃ N, N = TU 1 * M₁ * TU 1 := ⟨_, rfl⟩
  have hN : ∀ y, Φ W • y = OnePoint.Proj.mob N y := by
    intro y
    simp only [W]
    rw [hΦ, hΦ, hU, hL, hU, hNdef, mob_mul (hTUdet 1), mob_mul hM1det]
    push_cast
    rfl
  have hNdet : N.det ≠ 0 := by
    rw [hNdef, hM₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
      det_TU, det_TL, det_TU, det_TU]; norm_num
  have hNN : ∀ y, OnePoint.Proj.mob (N * N) y = y := by
    intro y
    rw [mob_mul hNdet, ← hN, ← hN, ← hΦ, hW, hneg]
  have hsc := scalar_of_three_fixed (x := ((0 : ℂ) : OnePoint ℂ)) (y := ((1 : ℂ) : OnePoint ℂ))
    (z := ∞) (by rw [Matrix.det_mul]; exact mul_ne_zero hNdet hNdet) (by simp) (by simp)
    (by simp) (hNN _) (hNN _) (hNN _)
  have h10 := congrFun (congrFun hsc 1) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    smul_zero] at h10
  have hNe : N = TU (1 + d) * TL b * TU (1 - d) := by
    simp only [hNdef, hM₁, ← Matrix.mul_assoc, hTU]
    simp only [Matrix.mul_assoc, hTU]
    congr 2; ring
  rw [hNe] at h10
  simp [TU, TL] at h10
  have hb : b ≠ 0 := by
    simp only [b]
    refine mul_ne_zero (neg_ne_zero.2 (pow_ne_zero _ (by rw [hG10]; exact hσr))) ?_
    exact_mod_cast (one_div_ne_zero (pow_ne_zero 2 hr))
  have hb' : b = -1 := by
    have : b * (2 + 2 * b) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb
    · linear_combination h / 2
  simp only [b, hG10] at hb'
  have hr2 : ((r : ℝ) : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 hr
  push_cast at hb'
  rw [neg_mul, neg_inj, one_div, ← div_eq_mul_inv, div_eq_one_iff_eq hr2] at hb'
  exact hb'

end complex

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
