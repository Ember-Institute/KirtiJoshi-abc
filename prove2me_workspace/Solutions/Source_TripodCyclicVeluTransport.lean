/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicIsogeny.lean (finite_crude and infinite_bound)
-/
import Solutions.Source_TripodCyclicVeluDescent
import Solutions.Source_TripodCyclicVeluFinite
import Solutions.Source_TripodRelativeAbsoluteValue
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Cyclic

open AbcAdaptation.Reference.Iut NumberField WeierstrassCurve
open JoshiTeich.Act1Scene1.IutCyclicVelu (veluRatio)
open scoped Classical

attribute [local instance 1100] JoshiTeich.ReferenceIut.instDecidableEqIntermediateField

private lemma max_one_pow {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    max 1 a ^ d = max 1 (a ^ d) := by
  rcases le_total a 1 with h | h
  · rw [max_eq_left h, one_pow, max_eq_left (pow_le_one₀ ha h)]
  · rw [max_eq_right h, max_eq_right (one_le_pow₀ h)]

lemma infinitePlace_apply_neg {F : Type*} [Field F] (v : InfinitePlace F) (y : F) :
    v (-y) = v y := by
  rw [← InfinitePlace.norm_embedding_eq, map_neg, norm_neg, InfinitePlace.norm_embedding_eq]

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime)
variable (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar)))

local instance (priority := 1100) veluTransportNumberField : NumberField ↥(L P x hℓ) :=
  (P.modRep x ℓ hℓ).numberField_torsionField

local instance veluTransportIsElliptic : (WL P x hℓ).IsElliptic := by
  letI : (P.curve x).E.IsElliptic := (P.curve x).isElliptic
  change ((P.curve x).E.map (algebraMap (P.curve x).F (L P x hℓ))).IsElliptic
  infer_instance

variable [Fintype (HL P x hℓ H)] {ρ : (P.curve x).F}
variable (hρ : algebraMap (P.curve x).F (L P x hℓ) ρ =
  veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
    veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ))

include hρ in
/-- The finite-place Vélu estimate on the descended product of ratios. -/
theorem finite_crude (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (v : FinitePlace (P.curve x).F) :
    v ρ * (v (sqrtLam' P x) * v (sqrtOneSubLam' P x) * v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ 4) ≤
      max 1 (v (genC' P x)) ^ 4 := by
  obtain ⟨w, hwv⟩ := FinitePlace.exists_liesOver (K := L P x hℓ) v
  let d := relLocalDeg w v
  have hd : d ≠ 0 := relLocalDeg_ne_zero hwv
  have htr (y : (P.curve x).F) : w (algebraMap (P.curve x).F (L P x hℓ) y) = v y ^ d :=
    apply_algebraMap_eq_pow hwv y
  have hl0 : lamL P x hℓ ≠ 0 := (map_ne_zero _).2 (genC'_ne_zero P x)
  have hcard := card_HL P x hℓ H hH
  have c₁ := crude_bound (HL P x hℓ H) (WL_eq P x hℓ) hl0 hℓ hℓ2 hcard w
    (T₁_ne_zero P x hℓ) (T₁_add_self P x hℓ) (R₁_add_self P x hℓ)
  have c₂ := crude_bound (HL P x hℓ H) (WL_eq P x hℓ) hl0 hℓ hℓ2 hcard w
    (T₂_ne_zero P x hℓ) (T₂_add_self P x hℓ) (R₂_add_self P x hℓ)
  rw [xCoordinate_T₁_sub_R₁ P x hℓ, map_neg_eq_map] at c₁
  rw [xCoordinate_T₂_sub_R₂ P x hℓ, map_neg_eq_map] at c₂
  rw [← map_natCast (algebraMap (P.curve x).F (L P x hℓ)) (4 * ℓ)] at c₁ c₂
  have hmax := max_one_pow (apply_nonneg v (genC' P x)) d
  simp only [lamL, htr, ← hmax] at c₁ c₂
  have hprod : (v ρ * (v (sqrtLam' P x) * v (sqrtOneSubLam' P x) *
      v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ 4)) ^ d ≤ (max 1 (v (genC' P x)) ^ 4) ^ d := by
    rw [mul_pow, ← htr ρ, hρ, map_mul]
    calc
      _ = (w (veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ)) * v (sqrtLam' P x) ^ d *
            (v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ d) ^ 2) *
          (w (veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ)) * v (sqrtOneSubLam' P x) ^ d *
            (v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ d) ^ 2) := by ring
      _ ≤ (max 1 (v (genC' P x)) ^ d) ^ 2 * (max 1 (v (genC' P x)) ^ d) ^ 2 :=
        mul_le_mul c₁ c₂
          (mul_nonneg (mul_nonneg (apply_nonneg w _) (pow_nonneg (apply_nonneg v _) _))
            (sq_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  have hnonneg : 0 ≤ v ρ * (v (sqrtLam' P x) * v (sqrtOneSubLam' P x) *
      v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ 4) :=
    mul_nonneg (apply_nonneg v _) (mul_nonneg
      (mul_nonneg (apply_nonneg v _) (apply_nonneg v _)) (pow_nonneg (apply_nonneg v _) _))
  exact (pow_le_pow_iff_left₀ hnonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) hd).mp hprod

include hρ in
/-- The archimedean estimate on the descended product using the same torsion bound. -/
theorem infinite_bound (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) {c C₀ : ℝ}
    (hC₀ : LegendreTorsionXBound c C₀) (v : InfinitePlace (P.curve x).F)
    (hv₁ : |Real.log (v (genC' P x))| ≤ c) (hv₂ : |Real.log (v (genC' P x - 1))| ≤ c) :
    v ρ * (v (sqrtLam' P x) * v (sqrtOneSubLam' P x)) ≤ (2 * ℓ * (C₀ * (4 * ℓ) ^ 2)) ^ 2 := by
  obtain ⟨w, hwv⟩ := InfinitePlace.comap_surjective (K := L P x hℓ) v
  have htr (y : (P.curve x).F) : w (algebraMap (P.curve x).F (L P x hℓ) y) = v y := by
    rw [← hwv, InfinitePlace.comap_apply]
  have hw₁ : |Real.log (w (lamL P x hℓ))| ≤ c := by
    simpa only [lamL, htr] using hv₁
  have hw₂ : |Real.log (w (lamL P x hℓ - 1))| ≤ c := by
    rw [lamL, ← map_one (algebraMap (P.curve x).F (L P x hℓ)), ← map_sub, htr]
    exact hv₂
  have hcard := card_HL P x hℓ H hH
  have a₁ := arch_bound (HL P x hℓ H) (WL_eq P x hℓ) hℓ hℓ2 hcard hC₀ w hw₁ hw₂
    (T₁_ne_zero P x hℓ) (T₁_add_self P x hℓ) (R₁_add_self P x hℓ)
  have a₂ := arch_bound (HL P x hℓ H) (WL_eq P x hℓ) hℓ hℓ2 hcard hC₀ w hw₁ hw₂
    (T₂_ne_zero P x hℓ) (T₂_add_self P x hℓ) (R₂_add_self P x hℓ)
  rw [xCoordinate_T₁_sub_R₁ P x hℓ, infinitePlace_apply_neg, htr] at a₁
  rw [xCoordinate_T₂_sub_R₂ P x hℓ, infinitePlace_apply_neg, htr] at a₂
  rw [← htr ρ, hρ, map_mul]
  calc
    _ = (w (veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ)) * v (sqrtLam' P x)) *
        (w (veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ)) * v (sqrtOneSubLam' P x)) := by ring
    _ ≤ _ * _ := mul_le_mul a₁ a₂ (mul_nonneg (apply_nonneg w _) (apply_nonneg v _))
      ((mul_nonneg (apply_nonneg w _) (apply_nonneg v _)).trans a₁)
    _ = _ := (pow_two _).symm

end AbcAdaptation.Tripod.Cyclic
