/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/HemiUnique.lean, `hemi_poly_unique`
-/
import Solutions.Source_ReferenceIutCanLiftPolynomialDegree
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Polynomial
open scoped BigOperators

section Affine

variable {W : WeierstrassCurve ℂ} [W.IsElliptic]

/-- The `2`-division cubic as a polynomial. -/
noncomputable abbrev tq (W : WeierstrassCurve ℂ) : ℂ[X] := W.twoTorsionPolynomial.toPoly

/-- The roots of the `2`-division cubic. -/
noncomputable def E₂ (W : WeierstrassCurve ℂ) : Finset ℂ := (tq W).roots.toFinset

omit [W.IsElliptic] in
lemma tq_eval (y : ℂ) : (tq W).eval y = 4 * y ^ 3 + W.b₂ * y ^ 2 + 2 * W.b₄ * y + W.b₆ := by
  simp [tq, WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly]

omit [W.IsElliptic] in
lemma tq_natDegree : (tq W).natDegree = 3 :=
  Cubic.natDegree_of_a_ne_zero (by simp [WeierstrassCurve.twoTorsionPolynomial])

omit [W.IsElliptic] in
lemma tq_ne_zero : tq W ≠ 0 := by
  intro h; have := tq_natDegree (W := W); rw [h, natDegree_zero] at this; omega

lemma tq_roots_nodup : (tq W).roots.Nodup := by
  have hd : W.twoTorsionPolynomial.discr ≠ 0 := by
    rw [WeierstrassCurve.twoTorsionPolynomial_discr]
    exact mul_ne_zero (by norm_num) W.isUnit_Δ.ne_zero
  have := (Cubic.discr_ne_zero_iff_roots_nodup (φ := RingHom.id ℂ)
    (by simp [WeierstrassCurve.twoTorsionPolynomial]) (IsAlgClosed.splits _)).mp hd
  simpa [Cubic.map, Cubic.roots, tq] using this

lemma card_E₂ : (E₂ W).card = 3 := by
  rw [E₂, Multiset.toFinset_card_of_nodup tq_roots_nodup,
    IsAlgClosed.card_roots_eq_natDegree, tq_natDegree]

lemma tq_eval_eq_prod (y : ℂ) : (tq W).eval y = 4 * ∏ e ∈ E₂ W, (y - e) := by
  have h := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := tq W))
  have hlc : (tq W).leadingCoeff = 4 :=
    Cubic.leadingCoeff_of_a_ne_zero (by simp [WeierstrassCurve.twoTorsionPolynomial])
  conv_lhs => rw [← h]
  rw [eval_mul, eval_C, hlc, eval_multiset_prod, E₂, Finset.prod_eq_multiset_prod,
    Multiset.toFinset_val, Multiset.dedup_eq_self.mpr tq_roots_nodup, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun e _ ↦ by simp

/-- An affine map permuting the `2`-division roots multiplies the cubic by `a³`. -/
lemma tq_affine {a b : ℂ} (ha : a ≠ 0) (hE : ∀ w ∈ E₂ W, a * w + b ∈ E₂ W) (y : ℂ) :
    (tq W).eval (a * y + b) = a ^ 3 * (tq W).eval y := by
  rw [tq_eval_eq_prod, tq_eval_eq_prod]
  have hinj : Set.InjOn (fun w ↦ a * w + b) (E₂ W) := fun w _ w' _ hww' ↦ by
    simpa [ha] using hww'
  have himage : (E₂ W).image (fun w ↦ a * w + b) = E₂ W :=
    Finset.eq_of_subset_of_card_le (fun e he ↦ by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he; exact hE w hw)
      (by rw [Finset.card_image_of_injOn hinj])
  conv_lhs => rw [← himage, Finset.prod_image hinj]
  rw [Finset.prod_congr rfl fun w _ ↦ show a * y + b - (a * w + b) = a * (y - w) by ring,
    Finset.prod_mul_distrib, Finset.prod_const, card_E₂]
  ring

/-- **Uniqueness of the map to `hemi E`, polynomial part.** A non-constant `p ∈ ℂ[X]` étale for
the hemi-elliptic multiplicities on both sides is `X`, unless `j(W) ∈ {0, 1728}`. -/
theorem hemi_poly_unique {p : ℂ[X]} (hp : 0 < p.natDegree)
    (h : ∀ w, polynomialRamificationIdx p w * hemiMultiplicity (E₂ W) w =
      hemiMultiplicity (E₂ W) (p.eval w)) :
    p = X ∨ W.j = 0 ∨ W.j = 1728 := by
  classical
  have hD := natDegree_eq_one_of_etale hp card_E₂ h
  have hp' := eq_X_add_C_of_natDegree_le_one hD.le
  set a := p.coeff 1
  set b := p.coeff 0
  have ha : a ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr (show p ≠ 0 by rintro rfl; simp at hp)
    rwa [leadingCoeff, hD] at this
  have hev : ∀ w, p.eval w = a * w + b := fun w ↦ by
    rw [hp']; simp
  -- `p` maps `E₂` into `E₂`
  have hE : ∀ w ∈ E₂ W, a * w + b ∈ E₂ W := by
    intro w hw
    have h1 := h w
    rw [← hev]
    simp only [hemiMultiplicity, if_pos hw] at h1
    by_contra hc
    rw [if_neg hc] at h1
    have hpos := polynomialRamificationIdx_pos hp w
    omega
  have hq := tq_affine ha hE
  have h0 := hq 0
  have h1 := hq 1
  have hm1 := hq (-1)
  simp only [tq_eval] at h0 h1 hm1
  have hE2 : a ^ 2 * (12 * b + W.b₂ - a * W.b₂) = 0 := by linear_combination (h1 + hm1) / 2 - h0
  have hE2' : 12 * b + W.b₂ - a * W.b₂ = 0 :=
    (mul_eq_zero.mp hE2).resolve_left (pow_ne_zero _ ha)
  have hE1 : a * (6 * b ^ 2 + W.b₂ * b + W.b₄ - a ^ 2 * W.b₄) = 0 := by
    linear_combination (h1 - hm1) / 4
  have hE1' : 6 * b ^ 2 + W.b₂ * b + W.b₄ - a ^ 2 * W.b₄ = 0 :=
    (mul_eq_zero.mp hE1).resolve_left ha
  have hE0 : 4 * b ^ 3 + W.b₂ * b ^ 2 + 2 * W.b₄ * b + W.b₆ - a ^ 3 * W.b₆ = 0 := by
    linear_combination h0
  have hc4 : (a ^ 2 - 1) * W.c₄ = 0 := by
    rw [WeierstrassCurve.c₄]
    linear_combination (-a * W.b₂ - 12 * b - W.b₂) * hE2' + 24 * hE1'
  have hc6 : (a ^ 3 - 1) * W.c₆ = 0 := by
    rw [WeierstrassCurve.c₆]
    linear_combination (a ^ 2 * W.b₂ ^ 2 - 36 * a ^ 2 * W.b₄ + 12 * a * b * W.b₂ + a * W.b₂ ^ 2 +
      144 * b ^ 2 + 24 * b * W.b₂ + W.b₂ ^ 2) * hE2' - 36 * (12 * b + W.b₂) * hE1' + 216 * hE0
  by_cases hj0 : W.c₄ = 0
  · exact Or.inr (Or.inl (W.j_eq_zero hj0))
  by_cases hj1 : W.c₆ = 0
  · right; right
    have hrel := W.c_relation
    rw [hj1] at hrel
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
    have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    field_simp
    linear_combination -hrel
  left
  have ha2 : a ^ 2 = 1 := by
    have := (mul_eq_zero.mp hc4).resolve_right hj0; linear_combination this
  have ha3 : a ^ 3 = 1 := by
    have := (mul_eq_zero.mp hc6).resolve_right hj1; linear_combination this
  have ha1 : a = 1 := by
    have : a * a ^ 2 = a ^ 3 := by ring
    rw [ha2, ha3, mul_one] at this; exact this
  have hb : b = 0 := by rw [ha1] at hE2'; linear_combination hE2' / 12
  rw [hp', ha1, hb]
  simp

end Affine

end AbcAdaptation.Reference.Iut.Anabelian
