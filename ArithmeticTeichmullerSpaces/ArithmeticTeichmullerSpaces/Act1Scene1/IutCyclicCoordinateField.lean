/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Tripod/CurveOf.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `5c6b5909ffda4af24582dc746e74e43702edc1c2`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: reuses the coordinate-field construction already adapted in
IutFourTorsionSource. New local proofs include all subgroup coordinates, lift
the subgroup and the chosen pairs, and transport ratios and translated sums.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutFourTorsionVeluRatio
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTorsionNewton
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource

/-!
source-id: IUT-COR312-CYCLIC-COORDINATE-FIELD
fidelity: constructs a finite number field containing the actual finite
geometric subgroup and the same four-torsion pairs used in the ratio descent.
The point inclusion identifies the rational subgroup with the original one.
Both ratios and translated sums commute with this inclusion. The resulting
nonzero ratio product has the number-field product formula, and the actual
translated sums have Newton bounds outside the finite model exceptions.
The additive identity relating the two expressions and the remaining local,
archimedean and height estimates remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutCyclicCoordinate

open WeierstrassCurve NumberField IutCyclicVelu IutTorsionNewton
open scoped Classical

universe u
noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable (H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar))) [Fintype H]

/-- All coordinates of the given geometric subgroup and the geometric four-torsion. -/
def coordinates : Set Fbar := IutFourTorsion.coordinates E Fbar ∪
  ⋃ Q ∈ (H : Set (Affine.Point (Affine.baseChange E Fbar))), IutFourTorsion.coords E Fbar Q

/-- The actual common coordinate field for the subgroup and the auxiliary points. -/
def field : IntermediateField F Fbar := IntermediateField.adjoin F (coordinates E Fbar H)

lemma coordinates_finite : (coordinates E Fbar H).Finite := by
  apply (IutFourTorsion.coordinates_finite E Fbar).union
  exact (Set.toFinite (H : Set (Affine.Point (Affine.baseChange E Fbar)))).biUnion
    fun Q _ => by
      cases Q with
      | zero => exact Set.finite_empty
      | some x y _ => exact (Set.finite_singleton y).insert x

lemma finiteDimensional_field : FiniteDimensional F ↥(field E Fbar H) := by
  letI : Finite (coordinates E Fbar H) := (coordinates_finite E Fbar H).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

instance numberField_field : NumberField ↥(field E Fbar H) := by
  letI : FiniteDimensional F ↥(field E Fbar H) := finiteDimensional_field E Fbar H
  letI : CharZero ↥(field E Fbar H) :=
    charZero_of_injective_algebraMap (algebraMap F ↥(field E Fbar H)).injective
  letI : IsScalarTower ℚ F ↥(field E Fbar H) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  letI : FiniteDimensional ℚ ↥(field E Fbar H) := Module.Finite.trans F ↥(field E Fbar H)
  exact {}

lemma fourTorsionField_le : IutFourTorsion.field E Fbar ≤ field E Fbar H := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  exact IntermediateField.subset_adjoin F _ (Or.inl hx)

local instance fieldDecidableEq : DecidableEq ↥(field E Fbar H) := Classical.decEq _

/-- The actual point inclusion from the common coordinate field into the closure. -/
def pointMap : (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point →+
    (E.map (algebraMap F Fbar)).toAffine.Point :=
  Affine.Point.map (W' := E) (S := F) (IsScalarTower.toAlgHom F ↥(field E Fbar H) Fbar)

lemma pointMap_injective : Function.Injective (pointMap E Fbar H) :=
  Affine.Point.map_injective (IsScalarTower.toAlgHom F ↥(field E Fbar H) Fbar)

/-- Coordinates in the common field give an actual point over that field. -/
lemma exists_point_of_coords_subset (P : Affine.Point (Affine.baseChange E Fbar))
    (hP : IutFourTorsion.coords E Fbar P ⊆ field E Fbar H) :
    ∃ Q : (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point,
      pointMap E Fbar H Q = P := by
  cases P with
  | zero => exact ⟨0, rfl⟩
  | some x y h =>
    have hx := hP (by simp [IutFourTorsion.coords] : x ∈ IutFourTorsion.coords E Fbar
      (Affine.Point.some x y h))
    have hy := hP (by simp [IutFourTorsion.coords] : y ∈ IutFourTorsion.coords E Fbar
      (Affine.Point.some x y h))
    have hns : (Affine.baseChange E ↥(field E Fbar H)).Nonsingular
        (⟨x, hx⟩ : ↥(field E Fbar H)) ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular (W := E)
        (IsScalarTower.toAlgHom F ↥(field E Fbar H) Fbar).injective _ _).mp h
    exact ⟨Affine.Point.some _ _ hns, rfl⟩

lemma exists_point_of_mem_subgroup (P : Affine.Point (Affine.baseChange E Fbar)) (hP : P ∈ H) :
    ∃ Q : (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point,
      pointMap E Fbar H Q = P := by
  apply exists_point_of_coords_subset E Fbar H P
  intro x hx
  exact IntermediateField.subset_adjoin F _ (Or.inr (Set.mem_biUnion hP hx))

lemma exists_point_of_four_nsmul (P : Affine.Point (Affine.baseChange E Fbar)) (hP : 4 • P = 0) :
    ∃ Q : (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point,
      pointMap E Fbar H Q = P := by
  apply exists_point_of_coords_subset E Fbar H P
  intro x hx
  exact IntermediateField.subset_adjoin F _ (Or.inl (Set.mem_biUnion
    (AddSubgroup.torsionBy.nsmul_iff.mpr hP) hx))

/-- The subgroup over the common field is the preimage of the given geometric subgroup. -/
def subgroup : AddSubgroup (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point :=
  H.comap (pointMap E Fbar H)

def subgroupMap : subgroup E Fbar H →+ H where
  toFun Q := ⟨pointMap E Fbar H Q.1, Q.2⟩
  map_zero' := Subtype.ext (map_zero (pointMap E Fbar H))
  map_add' Q R := Subtype.ext (map_add (pointMap E Fbar H) Q.1 R.1)

/-- The rational subgroup and the original geometric subgroup are additively equivalent. -/
def subgroupEquiv : subgroup E Fbar H ≃+ H := AddEquiv.ofBijective (subgroupMap E Fbar H) (by
  constructor
  · intro Q R h
    apply Subtype.ext
    exact pointMap_injective E Fbar H (congrArg Subtype.val h)
  · intro Q
    obtain ⟨R, hR⟩ := exists_point_of_mem_subgroup E Fbar H Q.1 Q.2
    refine ⟨⟨R, ?_⟩, Subtype.ext hR⟩
    change pointMap E Fbar H R ∈ H
    rw [hR]
    exact Q.2)

@[simp] lemma subgroupEquiv_apply (Q : subgroup E Fbar H) :
    ((subgroupEquiv E Fbar H) Q).1 =
      pointMap E Fbar H Q.1 := rfl

instance subgroupFintype : Fintype (subgroup E Fbar H) :=
  Fintype.ofEquiv H (subgroupEquiv E Fbar H).symm.toEquiv

lemma card_subgroup : Fintype.card (subgroup E Fbar H) = Fintype.card H :=
  Fintype.card_congr (subgroupEquiv E Fbar H).toEquiv

/-- The same canonical closure pairs lift to the common coordinate field. -/
lemma exists_pointPairs :
    ∃ P : IutFourTorsionPointPairs (E.map (algebraMap F ↥(field E Fbar H))),
      pointMap E Fbar H P.T₁ = (IutFourTorsion.pointPairsInClosure E Fbar).T₁ ∧
      pointMap E Fbar H P.R₁ = (IutFourTorsion.pointPairsInClosure E Fbar).R₁ ∧
      pointMap E Fbar H P.T₂ = (IutFourTorsion.pointPairsInClosure E Fbar).T₂ ∧
      pointMap E Fbar H P.R₂ = (IutFourTorsion.pointPairsInClosure E Fbar).R₂ := by
  let P := IutFourTorsion.pointPairsInClosure E Fbar
  let b := pointMap E Fbar H
  have hb : Function.Injective b := pointMap_injective E Fbar H
  obtain ⟨T₁, hT₁⟩ := exists_point_of_four_nsmul E Fbar H P.T₁ P.four_nsmul_T₁
  obtain ⟨T₂, hT₂⟩ := exists_point_of_four_nsmul E Fbar H P.T₂ P.four_nsmul_T₂
  obtain ⟨R₁, hR₁⟩ := exists_point_of_four_nsmul E Fbar H P.R₁ P.four_nsmul_R₁
  obtain ⟨R₂, hR₂⟩ := exists_point_of_four_nsmul E Fbar H P.R₂ P.four_nsmul_R₂
  change b T₁ = P.T₁ at hT₁
  change b T₂ = P.T₂ at hT₂
  change b R₁ = P.R₁ at hR₁
  change b R₂ = P.R₂ at hR₂
  refine ⟨⟨T₁, R₁, T₂, R₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hT₁, hR₁, hT₂, hR₂⟩
  · intro h; apply P.T₁_ne_zero; rw [← hT₁, h, map_zero]
  · intro h; apply P.T₂_ne_zero; rw [← hT₂, h, map_zero]
  · intro h; apply P.T₁_ne_T₂; rw [← hT₁, ← hT₂, h]
  · apply hb; rw [map_add, map_zero, hT₁, P.T₁_add_self]
  · apply hb; rw [map_add, map_zero, hT₂, P.T₂_add_self]
  · apply hb; rw [map_add, hR₁, hT₁, P.R₁_add_self]
  · apply hb; rw [map_add, hR₂, hT₂, P.R₂_add_self]

def pointPairs : IutFourTorsionPointPairs (E.map (algebraMap F ↥(field E Fbar H))) :=
  (exists_pointPairs E Fbar H).choose

lemma pointPairs_spec :
    pointMap E Fbar H (pointPairs E Fbar H).T₁ = (IutFourTorsion.pointPairsInClosure E Fbar).T₁ ∧
    pointMap E Fbar H (pointPairs E Fbar H).R₁ = (IutFourTorsion.pointPairsInClosure E Fbar).R₁ ∧
    pointMap E Fbar H (pointPairs E Fbar H).T₂ = (IutFourTorsion.pointPairsInClosure E Fbar).T₂ ∧
    pointMap E Fbar H (pointPairs E Fbar H).R₂ = (IutFourTorsion.pointPairsInClosure E Fbar).R₂ :=
  (exists_pointPairs E Fbar H).choose_spec

lemma xCoordinate_pointMap (P : (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point) :
    xCoordinate (pointMap E Fbar H P) =
      algebraMap ↥(field E Fbar H) Fbar (xCoordinate P) := by
  cases P with
  | zero => exact (map_zero (algebraMap ↥(field E Fbar H) Fbar)).symm
  | some x y h => rfl

/-- The actual Vélu ratio commutes with the coordinate-field inclusion. -/
lemma algebraMap_veluRatio (T R : (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point) :
    algebraMap ↥(field E Fbar H) Fbar (veluRatio (subgroup E Fbar H) T R) =
      veluRatio H (pointMap E Fbar H T) (pointMap E Fbar H R) := by
  let e := subgroupEquiv E Fbar H
  unfold veluRatio
  rw [map_prod]
  refine Finset.prod_nbij' e e.symm ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    rw [mem_nonzeroPoints] at hQ ⊢
    intro h
    exact hQ (e.injective (h.trans (map_zero e).symm))
  · intro Q hQ
    rw [mem_nonzeroPoints] at hQ ⊢
    intro h
    exact hQ (e.symm.injective (h.trans (map_zero e.symm).symm))
  · intro Q _; exact e.symm_apply_apply Q
  · intro Q _; exact e.apply_symm_apply Q
  · intro Q _
    rw [map_div₀, map_sub, map_sub, ← xCoordinate_pointMap, ← xCoordinate_pointMap,
      ← xCoordinate_pointMap, map_add]
    rfl

/-! The common coordinate-field ratio has a representative in the smaller
four-torsion field whenever its two arguments are four-torsion.  The proof
uses the single-ratio Galois descent from `IutFourTorsionVeluRatio` and the
coordinate-field inclusion above; no completion norm or residue-degree law is
introduced here. -/
lemma exists_inclusion_eq_veluRatio_of_four_nsmul
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H)
    (T R : (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point)
    (hT : 4 • T = 0) (hR : 4 • R = 0) :
    ∃ ρ : ↥(IutFourTorsion.field E Fbar),
      IntermediateField.inclusion (fourTorsionField_le E Fbar H) ρ =
        veluRatio (subgroup E Fbar H) T R := by
  have hT' : 4 • pointMap E Fbar H T = 0 := by
    rw [← map_nsmul, hT, map_zero]
  have hR' : 4 • pointMap E Fbar H R = 0 := by
    rw [← map_nsmul, hR, map_zero]
  obtain ⟨ρ, hρ⟩ := IutFourTorsion.exists_algebraMap_eq_veluRatio_of_four_nsmul
    (E := E) (Fbar := Fbar) (H := H) hgal hT' hR'
  refine ⟨ρ, (algebraMap ↥(field E Fbar H) Fbar).injective ?_⟩
  change algebraMap ↥(IutFourTorsion.field E Fbar) Fbar ρ =
    algebraMap ↥(field E Fbar H) Fbar (veluRatio (subgroup E Fbar H) T R)
  rw [hρ, algebraMap_veluRatio]

/-- The actual translated sum commutes with the same subgroup inclusion. -/
lemma algebraMap_translatedSum (T R : (E.map (algebraMap F ↥(field E Fbar H))).toAffine.Point) :
    algebraMap ↥(field E Fbar H) Fbar (translatedSum (subgroup E Fbar H) T R) =
      translatedSum H (pointMap E Fbar H T) (pointMap E Fbar H R) := by
  unfold translatedSum
  rw [map_sub, map_sum, map_sum]
  congr 1
  · refine Fintype.sum_equiv (subgroupEquiv E Fbar H).toEquiv _ _ fun Q => ?_
    rw [← xCoordinate_pointMap, map_add]
    rfl
  · refine Fintype.sum_equiv (subgroupEquiv E Fbar H).toEquiv _ _ fun Q => ?_
    rw [← xCoordinate_pointMap, map_add]
    rfl

/-- The product over the rational subgroup uses precisely the lifted canonical pairs. -/
def ratioProduct : ↥(field E Fbar H) :=
  veluRatio (subgroup E Fbar H) (pointPairs E Fbar H).T₁ (pointPairs E Fbar H).R₁ *
    veluRatio (subgroup E Fbar H) (pointPairs E Fbar H).T₂ (pointPairs E Fbar H).R₂

lemma algebraMap_ratioProduct : algebraMap ↥(field E Fbar H) Fbar (ratioProduct E Fbar H) =
    IutFourTorsion.ratioProduct H := by
  rw [ratioProduct, map_mul, algebraMap_veluRatio, algebraMap_veluRatio]
  obtain ⟨hT₁, hR₁, hT₂, hR₂⟩ := pointPairs_spec E Fbar H
  rw [hT₁, hR₁, hT₂, hR₂]
  rfl

/-- Product formulas and Newton bounds now use the same actual subgroup and auxiliary pairs. -/
theorem ratioProduct_productFormula_and_Newton (hodd : Odd (Fintype.card H)) :
    ratioProduct E Fbar H ≠ 0 ∧
    algebraMap ↥(field E Fbar H) Fbar (ratioProduct E Fbar H) = IutFourTorsion.ratioProduct H ∧
    (∏ w : InfinitePlace ↥(field E Fbar H), (w (ratioProduct E Fbar H)) ^ w.mult) *
      ∏ᶠ w : FinitePlace ↥(field E Fbar H), w (ratioProduct E Fbar H) = 1 ∧
    (∀ S : Finset (FinitePlace ↥(field E Fbar H)),
      (∀ w : FinitePlace ↥(field E Fbar H), w (ratioProduct E Fbar H) ≠ 1 → w ∈ S) →
      (∑ w : InfinitePlace ↥(field E Fbar H), (w.mult : ℝ) * Real.log (w (ratioProduct E Fbar H))) +
        ∑ w ∈ S, Real.log (w (ratioProduct E Fbar H)) = 0) ∧
    ∀ w : FinitePlace ↥(field E Fbar H),
      w ∉ modelBadPlaces (E.map (algebraMap F ↥(field E Fbar H))) →
      (w ((4 * Fintype.card H : ℕ) : ↥(field E Fbar H)) ^ 2 *
        w (translatedSum (subgroup E Fbar H) (pointPairs E Fbar H).T₁
          (pointPairs E Fbar H).R₁) ≤ 1) ∧
      (w ((4 * Fintype.card H : ℕ) : ↥(field E Fbar H)) ^ 2 *
        w (translatedSum (subgroup E Fbar H) (pointPairs E Fbar H).T₂
          (pointPairs E Fbar H).R₂) ≤ 1) := by
  have hρ := algebraMap_ratioProduct E Fbar H
  have hρ0 : ratioProduct E Fbar H ≠ 0 := by
    intro h
    rw [h, map_zero] at hρ
    exact IutFourTorsion.ratioProduct_ne_zero H hodd hρ.symm
  refine ⟨hρ0, hρ, NumberField.prod_abs_eq_one hρ0,
    fun S hS => logProductFormula hρ0 S hS, ?_⟩
  intro w hw
  let P := pointPairs E Fbar H
  constructor
  · have h := translatedSum_le w (subgroup E Fbar H) hw P.T₁ P.R₁
      P.four_nsmul_T₁ P.four_nsmul_R₁
    simpa only [card_subgroup] using h
  · have h := translatedSum_le w (subgroup E Fbar H) hw P.T₂ P.R₂
      P.four_nsmul_T₂ P.four_nsmul_R₂
    simpa only [card_subgroup] using h

/-- Original-base Galois stability retains the smaller four-torsion-field representative. -/
lemma ratioProduct_eq_inclusion
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H) :
    ∃ ρ : ↥(IutFourTorsion.field E Fbar),
      IntermediateField.inclusion (fourTorsionField_le E Fbar H) ρ = ratioProduct E Fbar H := by
  obtain ⟨ρ, hρ⟩ := IutFourTorsion.exists_algebraMap_eq_ratioProduct H hgal
  refine ⟨ρ, (algebraMap ↥(field E Fbar H) Fbar).injective ?_⟩
  change algebraMap ↥(IutFourTorsion.field E Fbar) Fbar ρ =
    algebraMap ↥(field E Fbar H) Fbar (ratioProduct E Fbar H)
  rw [hρ, algebraMap_ratioProduct]

/-! The descended representative is now connected to the actual completion map
at a finite place above a four-torsion-field place.  The local algebra instance
is the ring-hom algebra induced by the intermediate-field inclusion; no norm
or residue-degree identity is asserted here. -/
theorem exists_completionEmbedding_eq_ratioProduct
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H) :
    letI : Algebra (↥(IutFourTorsion.field E Fbar)) (↥(field E Fbar H)) :=
      (IntermediateField.inclusion (fourTorsionField_le E Fbar H)).toRingHom.toAlgebra
    ∀ (v : NumberField.FinitePlace ↥(field E Fbar H))
      (w : NumberField.FinitePlace ↥(IutFourTorsion.field E Fbar)),
      (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) →
      ∃ ρ : ↥(IutFourTorsion.field E Fbar),
        iutEmbedCompletion (v := v) (w := w) hvw
            (NumberField.FinitePlace.embedding w.maximalIdeal ρ) =
          NumberField.FinitePlace.embedding v.maximalIdeal (ratioProduct E Fbar H) := by
  letI : Algebra (↥(IutFourTorsion.field E Fbar)) (↥(field E Fbar H)) :=
    (IntermediateField.inclusion (fourTorsionField_le E Fbar H)).toRingHom.toAlgebra
  intro v w hvw
  obtain ⟨ρ, hρ⟩ := ratioProduct_eq_inclusion E Fbar H hgal
  refine ⟨ρ, ?_⟩
  rw [← hρ]
  exact iutEmbedCompletion_embedding hvw ρ

/-! Consume the completion connection at the valuation level.  The exponent is
the relative ramification index attached to the chosen pair of finite places;
no residue-degree normalization is folded into this statement. -/
theorem exists_valuedEmbedding_eq_ratioProduct_pow
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H) :
    letI : Algebra (↥(IutFourTorsion.field E Fbar)) (↥(field E Fbar H)) :=
      (IntermediateField.inclusion (fourTorsionField_le E Fbar H)).toRingHom.toAlgebra
    ∀ (v : NumberField.FinitePlace ↥(field E Fbar H))
      (w : NumberField.FinitePlace ↥(IutFourTorsion.field E Fbar)),
      (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) →
      ∃ ρ : ↥(IutFourTorsion.field E Fbar),
        Valued.v (NumberField.FinitePlace.embedding v.maximalIdeal
          (ratioProduct E Fbar H)) =
          Valued.v (NumberField.FinitePlace.embedding w.maximalIdeal ρ) ^
            iutRelativeRamificationIndex (v := v) (w := w) := by
  letI : Algebra (↥(IutFourTorsion.field E Fbar)) (↥(field E Fbar H)) :=
    (IntermediateField.inclusion (fourTorsionField_le E Fbar H)).toRingHom.toAlgebra
  intro v w hvw
  obtain ⟨ρ, hρ⟩ := exists_completionEmbedding_eq_ratioProduct E Fbar H hgal v w hvw
  refine ⟨ρ, ?_⟩
  rw [← hρ, iutValuedEmbedCompletion]

/-! The valuation power law transfers the strict unit-ball condition.  This is
the threshold form needed by local bounds and does not choose a raw versus
degree-normalized norm presentation. -/
theorem exists_norm_lt_one_iff_ratioProduct
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H) :
    letI : Algebra (↥(IutFourTorsion.field E Fbar)) (↥(field E Fbar H)) :=
      (IntermediateField.inclusion (fourTorsionField_le E Fbar H)).toRingHom.toAlgebra
    ∀ (v : NumberField.FinitePlace ↥(field E Fbar H))
      (w : NumberField.FinitePlace ↥(IutFourTorsion.field E Fbar)),
      (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) →
      ∃ ρ : ↥(IutFourTorsion.field E Fbar),
        ‖NumberField.FinitePlace.embedding v.maximalIdeal
          (ratioProduct E Fbar H)‖ < 1 ↔
          ‖NumberField.FinitePlace.embedding w.maximalIdeal ρ‖ < 1 := by
  letI : Algebra (↥(IutFourTorsion.field E Fbar)) (↥(field E Fbar H)) :=
    (IntermediateField.inclusion (fourTorsionField_le E Fbar H)).toRingHom.toAlgebra
  intro v w hvw
  obtain ⟨ρ, hρ⟩ := exists_valuedEmbedding_eq_ratioProduct_pow E Fbar H hgal v w hvw
  refine ⟨ρ, ?_⟩
  rw [Valued.toNormedField.norm_lt_one_iff,
    Valued.toNormedField.norm_lt_one_iff, hρ]
  exact (pow_lt_one_iff_of_nonneg zero_le
    (iutRelativeRamificationIndex_ne_zero hvw))

end
end JoshiTeich.Act1Scene1.IutCyclicCoordinate
