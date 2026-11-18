/-
Adapted from Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean,
Iut/Cor312/ThetaData/TateStructureOfIso.lean and Iut/Cor312/ThetaData/TateStructure.lean.
Source snapshot 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8, lana-agents/iut.
Upstream commits e4777b2238f45be2e58c00b4d0213c0cb83405b9,
09d74a40f46688fa5e4eba46ead73cb37d6abbe2 and 76c7866b5bbc4adbd245a30af1a4fd05d32f8c3f,
respectively. Git author Christian Merten.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Solutions.Source_ReferenceIutTateIsomorphism
import Solutions.Source_ReferenceIutTateUniformization

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve Anabelian TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

section Transport

variable {k : Type*} [Field k] {W : WeierstrassCurve k}

lemma xCoord_eq_ptX (C : VariableChange k) (P : W.toAffine.Point) :
    xCoord C P = ptX (vcPoint C W P) := by
  cases P <;> rfl

lemma yCoord_eq_ptY (C : VariableChange k) (P : W.toAffine.Point) :
    yCoord C P = ptY (vcPoint C W P) := by
  cases P <;> rfl

variable [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

/-- Carry the uniformization and its coordinate laws along the change of model. -/
def TateStructure.ofVariableChangeWithUniformization
    (t : TateParameter k) (C : VariableChange k) (hC : C • W = t.tateCurve)
    (U : TateParameterUniformization t) : TateStructure W where
  t := t
  C := C
  hC := hC
  iso := (U.iso.trans (pointCongr hC).symm).trans (vcEquiv C W).symm
  iso_x u hu := by
    simp only [AddEquiv.trans_apply]
    rw [xCoord_eq_ptX, vcEquiv_symm_apply, ptX_pointCongr_symm]
    exact U.iso_x u hu
  iso_y u hu := by
    simp only [AddEquiv.trans_apply]
    rw [yCoord_eq_ptY, vcEquiv_symm_apply, ptY_pointCongr_symm]
    exact U.iso_y u hu

end Transport

section Torsion

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} {w : FinitePlace ↥K}

/-- Construct the Tate model at a bad place from the discriminant square root. -/
private theorem exists_tate_model_at_bad_place
    (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    (hw : IsBadPlace E K VBad w)
    (hSplitSquare : ∃ s : localCompletion w,
      s ^ 2 = emb K w (algebraMap F ↥K (-(E.c₄ * E.c₆)))) :
    ∃ (t : TateParameter (localCompletion w)) (D : VariableChange (localCompletion w)),
      D • curveKw E K w = t.tateCurve := by
  let v₀ : FinitePlace F := Tripod.placeUnder w
  have hmult₀ : HasMultiplicativeReductionAt E v₀ := mult_placeUnder E K hmult hw
  let C := (exists_variableChange_of_mult E v₀ hmult₀).choose
  have hC := (exists_variableChange_of_mult E v₀ hmult₀).choose_spec
  let Cw := (C.map (algebraMap F ↥K)).map (emb K w)
  have hCw : Cw • curveKw E K w = curveKw (C • E) K w :=
    (curveKw_variableChange E K C w).symm
  have hwv₀ : FinitePlace.LiesOver w v₀ := Tripod.liesOver_placeUnder w
  have hc₄ := norm_c₄_curveKw (C • E) K hwv₀ hC.2.1
  have hΔ := norm_Δ_curveKw (C • E) K hwv₀ hC.2.2
  have h2 := norm_two_curveKw E K hVBad hw
  have h12 := twelve_ne_zero w
  have h20 : (2 : localCompletion w) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact zero_ne_one h2
  have hc₄0 : (curveKw (C • E) K w).c₄ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc₄
    exact zero_ne_one hc₄
  have hsq : ∃ s : localCompletion w,
      s ^ 2 = -((curveKw E K w).c₄ * (curveKw E K w).c₆) := by
    rw [neg_c₄_mul_c₆_curveKw]
    exact hSplitSquare
  have hsqC := sq_neg_c₄_mul_c₆_variableChange (curveKw E K w) Cw hsq.choose_spec
  rw [hCw] at hsqC
  have hroot := exists_tangent_root_of_sq (curveKw (C • E) K w) h20 hc₄0 hsqC
  obtain ⟨t, D, hD, -⟩ :=
    exists_variableChange_tateCurve h2 h12 (curveKw (C • E) K w) hc₄ hΔ hroot
  refine ⟨t, D * Cw, ?_⟩
  rw [mul_smul, hCw, hD]

/-- Transport the uniformization of the selected Tate parameter to the original curve. -/
def tateStructureOfBadPlace
    (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    (hw : IsBadPlace E K VBad w)
    (hSplitSquare : ∃ s : localCompletion w,
      s ^ 2 = emb K w (algebraMap F ↥K (-(E.c₄ * E.c₆))))
    (uniformize : ∀ t : TateParameter (localCompletion w),
      (12 : localCompletion w) ≠ 0 → ‖(2 : localCompletion w)‖ = 1 →
      TateParameterUniformization t) :
    TateStructure (curveKw E K w) := by
  let model := exists_tate_model_at_bad_place E K hVBad hmult hw hSplitSquare
  let t := model.choose
  let C := model.choose_spec.choose
  exact TateStructure.ofVariableChangeWithUniformization t C model.choose_spec.choose_spec
    (uniformize t (twelve_ne_zero w) (norm_two_curveKw E K hVBad hw))

end Torsion

end

end AbcAdaptation.Reference.Iut
