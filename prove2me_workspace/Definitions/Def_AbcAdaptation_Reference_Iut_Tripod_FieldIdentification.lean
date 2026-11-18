/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The iut contributors
-/
/-
Uncompiled draft: source declaration bodies selected byte-for-byte; wrappers and imports adapted.
Original repository: https://github.com/lana-agents/iut
Original revision recorded by existing adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
This draft does not itself establish accepted AST-command provenance.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldInvariant
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open WeierstrassCurve NumberField Polynomial
open scoped IntermediateField
section Curve
variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

/-- `λ` as an element of the field `F_λ = (curveOf x h3 h5).F` of the curve. -/
noncomputable abbrev genC : (curveOf x h3 h5).F := gen' x.1

/-- `j(E_λ) ∈ ℚ(λ)`. -/
theorem j_mem_adjoin : (curveOf x h3 h5).E.j ∈ ℚ⟮genC x h3 h5⟯ := by
  have hg : genC x h3 h5 ∈ ℚ⟮genC x h3 h5⟯ := IntermediateField.mem_adjoin_simple_self ℚ _
  have h256 : (256 : (curveOf x h3 h5).F) ∈ ℚ⟮genC x h3 h5⟯ := by
    have : (256 : (curveOf x h3 h5).F) = ((256 : ℕ) : (curveOf x h3 h5).F) := by norm_num
    rw [this]
    exact IntermediateField.natCast_mem _ _
  haveI : (legendre (genC x h3 h5)).IsElliptic := (curveOf x h3 h5).isElliptic
  have hj : (curveOf x h3 h5).E.j = 256 * (genC x h3 h5 ^ 2 - genC x h3 h5 + 1) ^ 3 /
      (genC x h3 h5 ^ 2 * (genC x h3 h5 - 1) ^ 2) := legendre_j (l := genC x h3 h5)
  rw [hj]
  exact div_mem (mul_mem h256 (pow_mem (add_mem (sub_mem (pow_mem hg 2) hg) (one_mem _)) 3))
    (mul_mem (pow_mem hg 2) (pow_mem (sub_mem hg (one_mem _)) 2))

/-- The embedding `F_λ → ℚ̄` as a `ℚ`-algebra homomorphism (for the `ℚ`-algebra structure
of `F_λ` as a number field). -/
noncomputable def embC : (curveOf x h3 h5).F →ₐ[ℚ] Qbar :=
  RingHom.toRatAlgHom ((fieldOf' x.1).val.toRingHom : (curveOf x h3 h5).F →+* Qbar)

@[simp] theorem embC_apply (a : (curveOf x h3 h5).F) :
    embC x h3 h5 a = (fieldOf' x.1).val a := rfl

/-- `ℚ(λ) ⊆ F_λ` is isomorphic to `ℚ(λ) ⊆ ℚ̄`. -/
noncomputable def adjoinGenCEquiv : ℚ⟮genC x h3 h5⟯ ≃ₐ[ℚ] fieldOf x.1 :=
  (IntermediateField.equivMap ℚ⟮genC x h3 h5⟯ (embC x h3 h5)).trans
    (IntermediateField.equivOfEq (by
      rw [IntermediateField.adjoin_map, Set.image_singleton, embC_apply]
      rfl))

open scoped Classical in
/-- The `x`-coordinates of the `F_λ`-rational `2`-torsion points of `E_λ` are `0`, `1`,
`λ`. -/
theorem twoTorsionXOf_eq :
    twoTorsionXOf (curveOf x h3 h5).F (curveOf x h3 h5).E = {0, 1, genC x h3 h5} := by
  haveI : (legendre (genC x h3 h5)).IsElliptic := (curveOf x h3 h5).isElliptic
  ext a
  simp only [twoTorsionXOf, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, h, hP⟩
    rw [AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff] at hP
    have hP' : (2 : ℕ) • Affine.Point.some a b h = 0 := by rw [← natCast_zsmul]; exact hP
    have hb : b = 0 := (two_nsmul_some_eq_zero_iff (genC x h3 h5) h).mp hP'
    subst hb
    exact legendre_equation_y_zero _ ((Affine.nonsingular_iff _ _).mp h).1
  · intro ha
    have hE : (curveOf x h3 h5).E.toAffine.Equation a 0 := by
      rcases ha with rfl | rfl | rfl
      · exact legendre_equation_zero (genC x h3 h5)
      · exact legendre_equation_one (genC x h3 h5)
      · exact legendre_equation_self (genC x h3 h5)
    refine ⟨0, Affine.equation_iff_nonsingular.mp hE, ?_⟩
    rw [AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
    have := two_nsmul_some_zero (genC x h3 h5) (Affine.equation_iff_nonsingular.mp hE)
    rwa [← natCast_zsmul] at this

/-- **The tripodal field of `E_λ` is `ℚ(λ)`**: `F_tpd = ℚ(j, 0, 1, λ) = ℚ(λ)`. -/
theorem tripodalFieldOf_eq :
    tripodalFieldOf (curveOf x h3 h5).F (curveOf x h3 h5).E = ℚ⟮genC x h3 h5⟯ := by
  rw [tripodalFieldOf, twoTorsionXOf_eq]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨j_mem_adjoin x h3 h5, ?_⟩
    rintro a (rfl | rfl | rfl)
    · exact zero_mem _
    · exact one_mem _
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (by simp))

end Curve
end AbcAdaptation.Tripod
