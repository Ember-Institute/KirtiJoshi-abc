import Solutions.Source_ReferenceHeightsTorsionLattice
import Solutions.Source_ReferenceIutVariableChangePoint
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Transport of complex lattice torsion to the short Weierstrass model

This is the point and coordinate part of `Heights/TorsionArchimedean.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. For the change of variables, use
the existing additive equivalence on affine Weierstrass points.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open WeierstrassCurve
open AbcAdaptation.Reference.Iut.Anabelian
open scoped UpperHalfPlane Classical

/-- The short Weierstrass model of `(τ, 1)`, with affine coordinates
`(℘(z), ℘'(z)/2)`. -/
noncomputable def latticeCurve (τ : ℍ) : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(periodPair τ).g₂ / 4, -(periodPair τ).g₃ / 4⟩

theorem latticeCurve_discriminant (τ : ℍ) :
    (latticeCurve τ).Δ = (periodPair τ).g₂ ^ 3 - 27 * (periodPair τ).g₃ ^ 2 := by
  simp [latticeCurve, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  ring

/-- The additive uniformization of the lattice curve with its coordinate formulas. -/
def LatticePointUniformization (τ : ℍ) : Prop :=
  ∃ e : (ℂ ⧸ (periodPair τ).lattice.toAddSubgroup) ≃+ (latticeCurve τ).toAffine.Point,
    (∀ z : ℂ, z ∈ (periodPair τ).lattice → e (QuotientAddGroup.mk z) = 0) ∧
      ∀ z : ℂ, z ∉ (periodPair τ).lattice →
        ∃ h : (latticeCurve τ).toAffine.Nonsingular ((periodPair τ).weierstrassP z)
            ((periodPair τ).derivWeierstrassP z / 2),
          e (QuotientAddGroup.mk z) = Affine.Point.some _ _ h

private theorem exists_weierstrassP_of_torsion {τ : ℍ} (hUniform : LatticePointUniformization τ)
    {W' : WeierstrassCurve ℂ} (hW' : W' = latticeCurve τ) {N : ℕ} {x y : ℂ}
    (h : W'.toAffine.Nonsingular x y)
    (hP : N • (Affine.Point.some x y h : W'.toAffine.Point) = 0) :
    ∃ z : ℂ, z ∉ (periodPair τ).lattice ∧ (N : ℂ) * z ∈ (periodPair τ).lattice ∧
      x = (periodPair τ).weierstrassP z := by
  subst W'
  obtain ⟨e, hzero, hpoint⟩ := hUniform
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (e.symm (Affine.Point.some x y h))
  have hPz : e (QuotientAddGroup.mk z) = Affine.Point.some x y h :=
    (congrArg e hz).trans (e.apply_symm_apply _)
  have hzL : z ∉ (periodPair τ).lattice := by
    intro hmem
    exact Affine.Point.some_ne_zero h (hPz.symm.trans (hzero z hmem))
  have hNz : N • (QuotientAddGroup.mk z : ℂ ⧸ (periodPair τ).lattice.toAddSubgroup) = 0 := by
    apply e.injective
    rw [map_nsmul, hPz, hP, map_zero]
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hNz
  change N • z ∈ (periodPair τ).lattice at hNz
  obtain ⟨_, hcoords⟩ := hpoint z hzL
  exact ⟨z, hzL, by simpa only [nsmul_eq_mul] using hNz,
    (Affine.Point.some.inj (hPz.symm.trans hcoords)).1⟩

/-- The lattice estimate transported to the original affine torsion point. -/
theorem norm_x_sub_r_le {τ : ℍ} (hτ : τ ∈ ModularGroup.fd)
    (hUniform : LatticePointUniformization τ) {W : WeierstrassCurve ℂ}
    {C : VariableChange ℂ} (hC : C • W = latticeCurve τ) {N : ℕ} (hN : 1 ≤ N)
    {x y : ℂ} (h : W.toAffine.Nonsingular x y)
    (hP : N • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    ‖x - C.r‖ ≤ ‖(C.u : ℂ)‖ ^ 2 * (2 * N ^ 2 + 80 * ‖(τ : ℂ)‖ ^ 2 * latticeSumThree) := by
  have hP' : N • vcPoint C W (Affine.Point.some x y h) = 0 := by
    change N • (vcEquiv C W) (Affine.Point.some x y h) = 0
    rw [← map_nsmul, hP, map_zero]
  rw [vcPoint_some C W h] at hP'
  obtain ⟨z, hz, hNz, hx⟩ := exists_weierstrassP_of_torsion hUniform hC _ hP'
  have hx' : x - C.r = (C.u : ℂ) ^ 2 * (periodPair τ).weierstrassP z := by
    rw [← hx, vcX]
    field_simp [C.u.ne_zero]
  rw [hx', norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (norm_weierstrassP_torsion_le hτ hN hNz hz) (sq_nonneg _)

theorem r_eq_neg_b₂_div_twelve {τ : ℍ} {W : WeierstrassCurve ℂ}
    {C : VariableChange ℂ} (hC : C • W = latticeCurve τ) : C.r = -(W.b₂ / 12) := by
  have h := variableChange_b₂ W C
  rw [hC] at h
  have hzero : (latticeCurve τ).b₂ = 0 := by simp [latticeCurve, b₂]
  rw [hzero] at h
  have hu : ((C.u⁻¹ : ℂˣ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  have heq := (mul_eq_zero.mp h.symm).resolve_left hu
  linear_combination heq / 12

theorem norm_u_pow_twelve_mul_discriminant {τ : ℍ} {W : WeierstrassCurve ℂ}
    {C : VariableChange ℂ} (hC : C • W = latticeCurve τ) :
    ‖(C.u : ℂ)‖ ^ 12 * ‖(latticeCurve τ).Δ‖ = ‖W.Δ‖ := by
  have h := variableChange_Δ W C
  rw [hC] at h
  rw [h, norm_mul, ← mul_assoc, ← norm_pow, ← norm_mul, ← mul_pow,
    Units.val_inv_eq_inv_val, mul_inv_cancel₀ C.u.ne_zero, one_pow, norm_one, one_mul]

end AbcAdaptation.Reference.Heights
