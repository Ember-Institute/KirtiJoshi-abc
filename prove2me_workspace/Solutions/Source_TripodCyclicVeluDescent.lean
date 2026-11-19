/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicIsogeny.lean (card_HL, ratio descent, and product formula)
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCyclicVeluRatio
import Solutions.Source_TripodCyclicVeluPoints
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Cyclic

open AbcAdaptation.Reference.Iut WeierstrassCurve NumberField
open AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData (TFbar)
open JoshiTeich.Act1Scene1.IutCyclicVelu (veluRatio veluRatio_ne_zero xCoordinate mem_nonzeroPoints)
open scoped Classical

attribute [local instance 1100] JoshiTeich.ReferenceIut.instDecidableEqIntermediateField

noncomputable section

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime)
variable (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar)))

/-- The preimage of the geometric subgroup on the provider's torsion field. -/
abbrev HL : AddSubgroup (WL P x hℓ).toAffine.Point :=
  H.comap (P.modRep x ℓ hℓ).bcK

private def subgroupEquiv (hH : Nat.card H = ℓ) : HL P x hℓ H ≃+ H := by
  let R := P.modRep x ℓ hℓ
  let f : HL P x hℓ H →+ H :=
    { toFun := fun Q => ⟨R.bcK Q.1, Q.2⟩
      map_zero' := Subtype.ext (map_zero R.bcK)
      map_add' Q S := Subtype.ext (map_add R.bcK Q.1 S.1) }
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro Q S h
    exact Subtype.ext (R.bcK_injective (congrArg Subtype.val h))
  · intro Q
    have hHle : H ≤ TFbar (P.curve x) ℓ :=
      JoshiTeich.Act1Scene1.iut_le_torsionBy_of_card_eq
        (E := (P.curve x).E) (Fbar := (P.curve x).Fbar) (H := H) hH
    obtain ⟨Q', hQ'⟩ := R.exists_bcK_eq Q.1 (hHle Q.2)
    have hmem : Q' ∈ HL P x hℓ H := by
      change R.bcK Q' ∈ H
      rw [hQ']
      exact Q.2
    exact ⟨⟨Q', hmem⟩, Subtype.ext hQ'⟩

/-- Every point of the geometric subgroup is rational over the torsion field. -/
lemma card_HL (hH : Nat.card H = ℓ) : Nat.card (HL P x hℓ H) = ℓ :=
  (Nat.card_congr (subgroupEquiv P x hℓ H hH).toEquiv).trans hH

lemma finite_HL (hH : Nat.card H = ℓ) : Finite (HL P x hℓ H) :=
  Nat.finite_of_card_ne_zero (by rw [card_HL P x hℓ H hH]; exact hℓ.ne_zero)

private lemma xCoordinate_bcK (Q : (WL P x hℓ).toAffine.Point) :
    xCoordinate ((P.modRep x ℓ hℓ).bcK Q) =
      algebraMap (L P x hℓ) (P.curve x).Fbar (xCoordinate Q) := by
  cases Q with
  | zero => exact (map_zero (algebraMap (L P x hℓ) (P.curve x).Fbar)).symm
  | some a b h => rfl

variable [Fintype (HL P x hℓ H)]

/-- The inclusion into the closure transports the ratio on the same subgroup. -/
lemma algebraMap_veluRatio [Fintype H] (hH : Nat.card H = ℓ)
    (T R : (WL P x hℓ).toAffine.Point) :
    algebraMap (L P x hℓ) (P.curve x).Fbar (veluRatio (HL P x hℓ H) T R) =
      veluRatio H ((P.modRep x ℓ hℓ).bcK T) ((P.modRep x ℓ hℓ).bcK R) := by
  let e := subgroupEquiv P x hℓ H hH
  unfold veluRatio
  rw [map_prod]
  refine Finset.prod_equiv e.toEquiv ?_ ?_
  · intro Q
    rw [mem_nonzeroPoints, mem_nonzeroPoints]
    change Q ≠ 0 ↔ e Q ≠ 0
    constructor
    · intro hQ h
      exact hQ (e.injective (h.trans (map_zero e).symm))
    · intro hQ h
      exact hQ (by rw [h, map_zero])
  · intro Q _
    rw [map_div₀, map_sub, map_sub, ← xCoordinate_bcK, ← xCoordinate_bcK,
      ← xCoordinate_bcK]
    let f := (P.modRep x ℓ hℓ).bcK
    exact congrArg (fun S =>
      (xCoordinate (f T) - xCoordinate S) /
        (xCoordinate (f T) - xCoordinate (f Q.1))) (map_add f R Q.1)

lemma odd_card_HL (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) :
    Odd (Fintype.card (HL P x hℓ H)) := by
  rw [Fintype.card_eq_nat_card, card_HL P x hℓ H hH]
  exact hℓ.odd_of_ne_two hℓ2

/-- Both designated ratios are nonzero over the torsion field. -/
lemma veluRatios_ne_zero (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) :
    veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) ≠ 0 ∧
      veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ) ≠ 0 := by
  have hodd := odd_card_HL P x hℓ H hH hℓ2
  exact ⟨veluRatio_ne_zero hodd (T₁_ne_zero P x hℓ) (T₁_add_self P x hℓ)
      (R₁_add_self P x hℓ),
    veluRatio_ne_zero hodd (T₂_ne_zero P x hℓ) (T₂_add_self P x hℓ)
      (R₂_add_self P x hℓ)⟩

/-- The product of the designated Vélu ratios descends to the original number
field, where it satisfies the logarithmic product formula. -/
theorem exists_ratio_logProductFormula (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2)
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H) :
    ∃ ρ : (P.curve x).F, ρ ≠ 0 ∧
      algebraMap (P.curve x).F (L P x hℓ) ρ =
        veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
          veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ) ∧
      ∀ S : Finset (FinitePlace (P.curve x).F),
        (∀ v : FinitePlace (P.curve x).F, v ρ ≠ 1 → v ∈ S) →
        (∑ v : InfinitePlace (P.curve x).F, (v.mult : ℝ) * Real.log (v ρ)) +
          ∑ v ∈ S, Real.log (v ρ) = 0 := by
  letI : Finite H := Nat.finite_of_card_ne_zero (hH.trans_ne hℓ.ne_zero)
  letI : Fintype H := Fintype.ofFinite H
  have hgal' : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H := by
    intro σ Q hQ
    simpa only [JoshiTeich.ReferenceIut.galPointMap, AbcAdaptation.Reference.Iut.galPointMap] using
      hgal σ Q hQ
  obtain ⟨ρ, hρ⟩ := JoshiTeich.Act1Scene1.IutCyclicVelu.exists_algebraMap_eq_ratio
    (E := (P.curve x).E) (Fbar := (P.curve x).Fbar) (H := H) hgal'
    (T₁Base P x) (R₁Base P x) (T₂Base P x) (R₂Base P x)
  have hρL : algebraMap (P.curve x).F (L P x hℓ) ρ =
      veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
        veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ) := by
    apply (algebraMap (L P x hℓ) (P.curve x).Fbar).injective
    rw [← IsScalarTower.algebraMap_apply (P.curve x).F (L P x hℓ) (P.curve x).Fbar,
      map_mul, algebraMap_veluRatio P x hℓ H hH, algebraMap_veluRatio P x hℓ H hH,
      T₁, R₁, T₂, R₂, bcK_baseChangeToL P x hℓ (T₁Base P x),
      bcK_baseChangeToL P x hℓ (R₁Base P x), bcK_baseChangeToL P x hℓ (T₂Base P x),
      bcK_baseChangeToL P x hℓ (R₂Base P x)]
    exact hρ
  obtain ⟨h₁, h₂⟩ := veluRatios_ne_zero P x hℓ H hH hℓ2
  have hρ0 : ρ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hρL
    exact mul_ne_zero h₁ h₂ hρL.symm
  exact ⟨ρ, hρ0, hρL, fun S hS =>
    JoshiTeich.Act1Scene1.IutCyclicVelu.logProductFormula hρ0 S hS⟩

end
end AbcAdaptation.Tripod.Cyclic
