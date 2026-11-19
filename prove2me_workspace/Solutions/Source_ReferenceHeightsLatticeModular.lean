import Solutions.Source_ReferenceHeightsTorsionCurve
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The modular invariants of the short lattice model

The normalization is from `Heights/LatticeEisenstein.lean`, `Heights/LatticeWeierstrass.lean`
and `Heights/ModularJ.lean` at `721496ca4c158e511d25d8ccf6bfe8503eda73c1`.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open EisensteinSeries WeierstrassCurve UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups Modular

private theorem latticeG_eq_modularE {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (periodPair τ).G k = 2 * riemannZeta k * ModularForm.E hk τ := by
  let pair := periodPair τ
  have hsum : pair.G k = ∑' v : Fin 2 → ℤ, eisSummand k v τ := by
    rw [PeriodPair.G, ← pair.latticeEquivProd.symm.toEquiv.tsum_eq,
      ← (LinearEquiv.finTwoArrow ℤ ℤ).toEquiv.tsum_eq]
    apply tsum_congr
    intro v
    change ((↑(pair.latticeEquivProd.symm (v 0, v 1)) : ℂ) ^ k)⁻¹ = eisSummand k v τ
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [pair, periodPair, eisSummand, zpow_neg]
  rw [hsum, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ]
  have hE : ModularForm.E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [hE]
  ring

private theorem zeta_six : riemannZeta (6 : ℂ) = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by decide)
  rw [show bernoulli 6 = 1 / 42 by decide +kernel] at h
  norm_num at h
  convert h using 1
  ring

private theorem lattice_g₂ (τ : ℍ) :
    (periodPair τ).g₂ = (4 * (Real.pi : ℂ) ^ 4 / 3) * ModularForm.E₄ τ := by
  rw [PeriodPair.g₂, latticeG_eq_modularE (by decide : 3 ≤ 4)]
  norm_num only [Nat.cast_ofNat]
  rw [riemannZeta_four]
  ring

private theorem lattice_g₃ (τ : ℍ) :
    (periodPair τ).g₃ = (8 * (Real.pi : ℂ) ^ 6 / 27) * ModularForm.E₆ τ := by
  rw [PeriodPair.g₃, latticeG_eq_modularE (by decide : 3 ≤ 6)]
  norm_num only [Nat.cast_ofNat]
  rw [zeta_six]
  ring

/-- Silverman's modular discriminant with its factor `(2π)^12`. -/
noncomputable def silvermanDiscriminant (τ : ℍ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ 12 * ModularForm.discriminant τ

/-- The modular `j)-function normalized by `E₄³/Δ`. -/
noncomputable def modularJ (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

theorem latticeCurve_discriminant_eq_silvermanDiscriminant (τ : ℍ) :
    (latticeCurve τ).Δ = silvermanDiscriminant τ := by
  rw [latticeCurve_discriminant, lattice_g₂, lattice_g₃, silvermanDiscriminant,
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

theorem latticeCurve_isElliptic (τ : ℍ) : (latticeCurve τ).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero,
    latticeCurve_discriminant_eq_silvermanDiscriminant, silvermanDiscriminant]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hπ))
    (ModularForm.discriminant_ne_zero τ)

theorem latticeCurve_j_eq_modularJ (τ : ℍ) [(latticeCurve τ).IsElliptic] :
    (latticeCurve τ).j = modularJ τ := by
  have hc₄ : (latticeCurve τ).c₄ = 12 * (periodPair τ).g₂ := by
    simp [latticeCurve, c₄, b₂, b₄]
    ring
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ', hc₄, lattice_g₂,
    latticeCurve_discriminant_eq_silvermanDiscriminant, silvermanDiscriminant, modularJ]
  field_simp [ModularForm.discriminant_ne_zero τ, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

open Matrix.SpecialLinearGroup CongruenceSubgroup in
theorem modularJ_smul (γ : SL(2, ℤ)) (τ : ℍ) : modularJ (γ • τ) = modularJ τ := by
  have hE : ModularForm.E₄ (γ • τ) = denom γ τ ^ (4 : ℤ) * ModularForm.E₄ τ := by
    letI : SlashInvariantFormClass (ModularForm 𝒮ℒ 4) Γ(1) 4 :=
      Gamma_one_coe_eq_SL ▸ inferInstance
    exact SlashInvariantForm.slash_action_eqn_SL'' ModularForm.E₄ (mem_Gamma_one γ) τ
  have hD : ModularForm.discriminant (γ • τ) =
      denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    letI : SlashInvariantFormClass (CuspForm 𝒮ℒ 12) Γ(1) 12 :=
      Gamma_one_coe_eq_SL ▸ inferInstance
    exact SlashInvariantForm.slash_action_eqn_SL'' CuspForm.discriminant (mem_Gamma_one γ) τ
  rw [modularJ, modularJ, hE, hD]
  field_simp [denom_ne_zero, ModularForm.discriminant_ne_zero]

theorem exists_mem_fd_modularJ_eq (hsurj : Function.Surjective modularJ) (j : ℂ) :
    ∃ τ : ℍ, τ ∈ ModularGroup.fd ∧ modularJ τ = j := by
  obtain ⟨τ, hτ⟩ := hsurj j
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  exact ⟨γ • τ, hγ, (modularJ_smul γ τ).trans hτ⟩

end AbcAdaptation.Reference.Heights
