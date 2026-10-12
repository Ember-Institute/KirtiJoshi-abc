import ArithmeticTeichmullerSpaces.Act1Scene1.IutFourTorsionSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCyclicVeluRatio

/-!
source-id: IUT-COR312-FOUR-TORSION-VELU-DESCENT
fidelity: consumes the geometric point pairs and their finite coordinate field.
An original-base Galois-stable subgroup gives a nonzero product of actual Vélu
ratios in that field. The product satisfies the number-field product formula
and its logarithmic form. The point pairs need no external rationality input.
These are local proofs using the sources recorded in the two imported modules.
Local estimates, height transport and the no-cyclic-subgroup bound remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutFourTorsion

open WeierstrassCurve NumberField IutCyclicVelu
open scoped Classical

universe u
noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

/-- The original closure is an algebraic closure of the four-torsion field. -/
lemma isAlgClosure_field : IsAlgClosure ↥(field E Fbar) Fbar :=
  ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩

/-- Choose the actual geometric pairs used in the ratio product. -/
def pointPairsInClosure : IutFourTorsionPointPairs (E.map (algebraMap F Fbar)) := by
  letI : CharZero Fbar := charZero_of_injective_algebraMap (algebraMap F Fbar).injective
  letI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  exact iutGeometricFourTorsionPointPairs (E.map (algebraMap F Fbar))

/-- Automorphisms over the coordinate field fix every geometric four-torsion point. -/
lemma galPointMap_eq_of_four_nsmul
    (σ : Fbar ≃ₐ[↥(field E Fbar)] Fbar)
    (P : Affine.Point (Affine.baseChange E Fbar)) (hP : 4 • P = 0) :
    JoshiTeich.ReferenceIut.galPointMap F E Fbar (σ.restrictScalars F) P = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    have hx : x ∈ field E Fbar := IntermediateField.subset_adjoin F _
      (Set.mem_biUnion (x := Affine.Point.some x y h)
        (AddSubgroup.torsionBy.nsmul_iff.mpr hP) (by simp [coords]))
    have hy : y ∈ field E Fbar := IntermediateField.subset_adjoin F _
      (Set.mem_biUnion (x := Affine.Point.some x y h)
        (AddSubgroup.torsionBy.nsmul_iff.mpr hP) (by simp [coords]))
    have hxσ := σ.commutes (⟨x, hx⟩ : ↥(field E Fbar))
    have hyσ := σ.commutes (⟨y, hy⟩ : ↥(field E Fbar))
    change σ x = x at hxσ
    change σ y = y at hyσ
    change Affine.Point.some (σ x) (σ y) _ = _
    congr 1

variable {E Fbar}
variable (H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar))) [Fintype H]

/-- The product of the two ratios for the chosen geometric pairs. -/
def ratioProduct : Fbar :=
  veluRatio H (pointPairsInClosure E Fbar).T₁ (pointPairsInClosure E Fbar).R₁ *
    veluRatio H (pointPairsInClosure E Fbar).T₂ (pointPairsInClosure E Fbar).R₂

/-- Odd subgroup order makes the actual ratio product nonzero. -/
lemma ratioProduct_ne_zero (hodd : Odd (Fintype.card H)) : ratioProduct H ≠ 0 := by
  let P := pointPairsInClosure E Fbar
  exact mul_ne_zero
    (veluRatio_ne_zero hodd P.T₁_ne_zero P.T₁_add_self P.R₁_add_self)
    (veluRatio_ne_zero hodd P.T₂_ne_zero P.T₂_add_self P.R₂_add_self)

/-- Original-base stability gives invariance over the four-torsion field. -/
lemma ratioProduct_galois
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H)
    (σ : Fbar ≃ₐ[↥(field E Fbar)] Fbar) : σ (ratioProduct H) = ratioProduct H := by
  let P := pointPairsInClosure E Fbar
  have hT₁ := galPointMap_eq_of_four_nsmul E Fbar σ P.T₁ P.four_nsmul_T₁
  have hR₁ := galPointMap_eq_of_four_nsmul E Fbar σ P.R₁ P.four_nsmul_R₁
  have hT₂ := galPointMap_eq_of_four_nsmul E Fbar σ P.T₂ P.four_nsmul_T₂
  have hR₂ := galPointMap_eq_of_four_nsmul E Fbar σ P.R₂ P.four_nsmul_R₂
  change (σ.restrictScalars F) (veluRatio H P.T₁ P.R₁ * veluRatio H P.T₂ P.R₂) = _
  rw [map_mul, veluRatio_galois hgal (σ.restrictScalars F) hT₁ hR₁,
    veluRatio_galois hgal (σ.restrictScalars F) hT₂ hR₂]
  rfl

/-- The actual ratio product descends to the finite four-torsion coordinate field. -/
lemma exists_algebraMap_eq_ratioProduct
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H) :
    ∃ ρ : ↥(field E Fbar), algebraMap ↥(field E Fbar) Fbar ρ = ratioProduct H := by
  letI : IsAlgClosure ↥(field E Fbar) Fbar := isAlgClosure_field E Fbar
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ↥(field E Fbar)) _).mpr
    (ratioProduct_galois H hgal)

/-- A Vélu ratio whose two arguments are four-torsion descends to the same
coordinate field as the geometric four-torsion points.  This is the
single-ratio form of the product descent above; it keeps the subgroup
stability hypothesis explicit and does not assert any completion norm law. -/
lemma exists_algebraMap_eq_veluRatio_of_four_nsmul
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H)
    {T R : Affine.Point (Affine.baseChange E Fbar)}
    (hT : 4 • T = 0) (hR : 4 • R = 0) :
    ∃ ρ : ↥(field E Fbar), algebraMap ↥(field E Fbar) Fbar ρ =
      veluRatio H T R := by
  letI : IsAlgClosure ↥(field E Fbar) Fbar := isAlgClosure_field E Fbar
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ↥(field E Fbar)) _).mpr
  intro σ
  exact veluRatio_galois hgal (σ.restrictScalars F)
    (galPointMap_eq_of_four_nsmul E Fbar σ T hT)
    (galPointMap_eq_of_four_nsmul E Fbar σ R hR)

/-- Actual geometric pairs supply a nonzero ratio and both product formulas. -/
theorem exists_nonzero_ratio_productFormula
    (hodd : Odd (Fintype.card H))
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H) :
    ∃ ρ : ↥(field E Fbar), ρ ≠ 0 ∧
      algebraMap ↥(field E Fbar) Fbar ρ = ratioProduct H ∧
      (∏ w : InfinitePlace ↥(field E Fbar), (w ρ) ^ w.mult) *
        ∏ᶠ w : FinitePlace ↥(field E Fbar), w ρ = 1 ∧
      ∀ S : Finset (FinitePlace ↥(field E Fbar)),
        (∀ w : FinitePlace ↥(field E Fbar), w ρ ≠ 1 → w ∈ S) →
        (∑ w : InfinitePlace ↥(field E Fbar), (w.mult : ℝ) * Real.log (w ρ)) +
          ∑ w ∈ S, Real.log (w ρ) = 0 := by
  obtain ⟨ρ, hρ⟩ := exists_algebraMap_eq_ratioProduct H hgal
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, map_zero] at hρ
    exact ratioProduct_ne_zero H hodd hρ.symm
  exact ⟨ρ, hρ0, hρ, NumberField.prod_abs_eq_one hρ0,
    fun S hS => logProductFormula hρ0 S hS⟩

end
end JoshiTeich.Act1Scene1.IutFourTorsion
