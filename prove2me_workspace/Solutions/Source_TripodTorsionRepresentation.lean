/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/-
Original repository https://github.com/lana-agents/iut
Original path Iut/Tripod/TorsionDegree.lean
-/
import Solutions.Source_TripodTorsionAction
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve
open scoped Classical IntermediateField

section Representation

variable (K : IntermediateField ℚ Qbar) {l : Qbar} (hl : l ∈ K) (n : ℕ)
variable (b : AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n))

/-- The `ℤ/n`-linear endomorphism `b ∘ σ ∘ b⁻¹` of `(ℤ/n)²` induced by `σ ∈ Gal(ℚ̄/K)`. -/
noncomputable def repLin (σ : Qbar ≃ₐ[K] Qbar) : Module.End (ZMod n) (Fin 2 → ZMod n) :=
  (b.toAddMonoidHom.comp ((galTorsion K hl n σ).comp b.symm.toAddMonoidHom)).toZModLinearMap n

theorem repLin_apply (σ : Qbar ≃ₐ[K] Qbar) (v : Fin 2 → ZMod n) :
    repLin K hl n b σ v = b (galTorsion K hl n σ (b.symm v)) :=
  rfl

/-- `σ ↦ b ∘ σ ∘ b⁻¹` as a monoid homomorphism to the endomorphisms of `(ℤ/n)²`. -/
noncomputable def repEnd : (Qbar ≃ₐ[K] Qbar) →* Module.End (ZMod n) (Fin 2 → ZMod n) where
  toFun := repLin K hl n b
  map_one' := by
    refine LinearMap.ext fun v => ?_
    rw [repLin_apply, Module.End.one_apply]
    have h : galTorsion K hl n 1 (b.symm v) = b.symm v := Subtype.ext (galAct_one K hl _)
    rw [h, b.apply_symm_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, repLin_apply, repLin_apply, repLin_apply, b.symm_apply_apply]
    congr 1
    exact Subtype.ext (galAct_mul K hl σ τ _)

/-- **The mod-`n` representation** `ρ : Gal(ℚ̄/K) →* GL₂(ℤ/n)` of the Legendre curve in the
basis `b` of `E_λ(ℚ̄)[n]`. -/
noncomputable def torsionRep : (Qbar ≃ₐ[K] Qbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod n) :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv' :
    Module.End (ZMod n) (Fin 2 → ZMod n) ≃ₐ[ZMod n] Matrix (Fin 2) (Fin 2) (ZMod n)).toMulEquiv
    ).toMonoidHom.comp (repEnd K hl n b).toHomUnits

/-- `σ ∈ ker ρ` iff `σ` fixes every `n`-torsion point. -/
theorem mem_torsionRep_ker_iff (σ : Qbar ≃ₐ[K] Qbar) :
    σ ∈ (torsionRep K hl n b).ker ↔
      ∀ P : AddSubgroup.torsionBy (legendre l).toAffine.Point n, galAct K hl σ P = P := by
  rw [MonoidHom.mem_ker, torsionRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one]
  change repLin K hl n b σ = 1 ↔ _
  constructor
  · intro h P
    have hv := LinearMap.congr_fun h (b P)
    rw [repLin_apply, b.symm_apply_apply, Module.End.one_apply] at hv
    exact congrArg Subtype.val (b.injective hv)
  · intro h
    refine LinearMap.ext fun v => ?_
    have hv : galTorsion K hl n σ (b.symm v) = b.symm v := Subtype.ext (h (b.symm v))
    rw [repLin_apply, Module.End.one_apply, hv, b.apply_symm_apply]

/-- **The kernel of `ρ` is the fixing subgroup of the torsion field** `K(E_λ[n])`. -/
theorem torsionRep_ker :
    (torsionRep K hl n b).ker =
      (IntermediateField.adjoin K (torsionCoords l n)).fixingSubgroup := by
  ext σ
  rw [mem_torsionRep_ker_iff, galAct_torsion_fixed_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem c hc => exact h c hc
    | algebraMap r => exact σ.commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  · intro h c hc
    exact h c (IntermediateField.subset_adjoin K _ hc)

end Representation

end AbcAdaptation.Tripod
