/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths: Iut/Tripod/CurveOf.lean and Iut/Tripod/CurveFacts.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve NumberField Polynomial
open scoped IntermediateField

theorem sqrtNegOne_sq : sqrtNegOne ^ 2 = -1 :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos).choose_spec

theorem sqrtLam_sq (l : Qbar) : sqrtLam l ^ 2 = l :=
  (IsAlgClosed.exists_pow_nat_eq l two_pos).choose_spec

theorem sqrtOneSubLam_sq (l : Qbar) : sqrtOneSubLam l ^ 2 = 1 - l :=
  (IsAlgClosed.exists_pow_nat_eq (1 - l) two_pos).choose_spec

/-- **The torsion degree bound**: for every number field `K ⊆ ℚ̄` containing `λ`, adjoining
the coordinates of the `n`-torsion of `E_λ` multiplies the degree by at most
`|GL₂(𝔽_n)| = (n² − 1)(n² − n)` (the `n`-torsion field `K(E_λ[n])` is Galois over `K` with
group embedded in `GL₂(ℤ/n)` by the action on a basis of `E_λ[n] ≅ (ℤ/n)²`). Recorded as a
`Prop`, not postulated. -/
def TorsionDegreeBound (l : Qbar) (n : ℕ) : Prop :=
  ∀ K : IntermediateField ℚ Qbar, FiniteDimensional ℚ K → l ∈ K →
    Module.finrank ℚ ↥(K ⊔ IntermediateField.adjoin ℚ (torsionCoords l n)) ≤
      (n ^ 2 - 1) * (n ^ 2 - n) * Module.finrank ℚ K

/-- `[K(s) : ℚ] ≤ 2·[K : ℚ]` for `s² ∈ K`. -/
theorem finrank_sup_adjoin_sq_le (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K]
    {s : Qbar} (hs : s ^ 2 ∈ K) :
    Module.finrank ℚ ↥(K ⊔ ℚ⟮s⟯) ≤ 2 * Module.finrank ℚ K := by
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  have hint : IsIntegral K s := (isIntegral s).tower_top
  have h2 : Module.finrank K K⟮s⟯ ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    have hmin := minpoly.min K s (monic_X_pow_sub_C (⟨s ^ 2, hs⟩ : K) two_ne_zero) (by simp)
    have := natDegree_le_natDegree hmin
    rwa [natDegree_X_pow_sub_C] at this
  calc Module.finrank ℚ ↥(IntermediateField.restrictScalars ℚ K⟮s⟯)
      = Module.finrank ℚ K * Module.finrank K K⟮s⟯ :=
        (Module.finrank_mul_finrank ℚ K K⟮s⟯).symm
    _ ≤ Module.finrank ℚ K * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Module.finrank ℚ K := mul_comm _ _

/-- `[ℚ(λ, √−1, √λ, √(1 − λ)) : ℚ] ≤ 8·[ℚ(λ) : ℚ]`. -/
theorem finrank_adjoin_gens_le (l : Qbar) :
    Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l}) ≤
      8 * deg l := by
  have hset : ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} : Set Qbar) =
      (({l} ∪ {sqrtNegOne}) ∪ {sqrtLam l}) ∪ {sqrtOneSubLam l} := by
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc]
  rw [hset, IntermediateField.adjoin_union, IntermediateField.adjoin_union,
    IntermediateField.adjoin_union]
  haveI : FiniteDimensional ℚ ℚ⟮sqrtNegOne⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral _)
  haveI : FiniteDimensional ℚ ℚ⟮sqrtLam l⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral _)
  have hl : l ∈ ℚ⟮l⟯ := IntermediateField.mem_adjoin_simple_self ℚ l
  have h1 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) ≤ 2 * deg l := by
    rw [deg_eq_finrank]
    exact finrank_sup_adjoin_sq_le _ (by rw [sqrtNegOne_sq]; exact neg_mem (one_mem _))
  have h2 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯) ≤
      2 * Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) :=
    finrank_sup_adjoin_sq_le _ (by rw [sqrtLam_sq]; exact le_sup_left (a := ℚ⟮l⟯) hl)
  have h3 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯ ⊔ ℚ⟮sqrtOneSubLam l⟯) ≤
      2 * Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯) :=
    finrank_sup_adjoin_sq_le _ (by
      rw [sqrtOneSubLam_sq]
      exact sub_mem (one_mem _)
        (le_sup_left (a := ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) (le_sup_left (a := ℚ⟮l⟯) hl)))
  omega

/-- **The degree bound** `[F_λ : ℚ] ≤ 552960·[ℚ(λ) : ℚ]` ((E3)–(E5) in the proof of IUT IV,
Theorem 1.10), from the torsion degree bounds for `n = 3` and `n = 5`:
`[F_λ : ℚ] ≤ 480·48·8·[ℚ(λ) : ℚ] = 184320·[ℚ(λ) : ℚ]`. -/
theorem deg_le (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)
    (hT3 : TorsionDegreeBound x.1 3) (hT5 : TorsionDegreeBound x.1 5) :
    Module.finrank ℚ (curveOf x h3 h5).F ≤ 552960 * deg x.1 := by
  set K₁ : IntermediateField ℚ Qbar :=
    IntermediateField.adjoin ℚ {x.1, sqrtNegOne, sqrtLam x.1, sqrtOneSubLam x.1} with hK₁
  set K₂ : IntermediateField ℚ Qbar :=
    K₁ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 3) with hK₂
  haveI hK₁fin : FiniteDimensional ℚ K₁ := by
    haveI := (Set.toFinite {x.1, sqrtNegOne, sqrtLam x.1, sqrtOneSubLam x.1}).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral y
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (torsionCoords x.1 3)) := by
    haveI := (torsionCoords_finite h3).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral y
  haveI hK₂fin : FiniteDimensional ℚ K₂ := IntermediateField.finiteDimensional_sup _ _
  have hl₁ : x.1 ∈ K₁ := IntermediateField.subset_adjoin _ _ (by simp)
  have hl₂ : x.1 ∈ K₂ := le_sup_left (a := K₁) hl₁
  have hF : fieldOf' x.1 = K₂ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 5) := by
    rw [fieldOf', IntermediateField.adjoin_union, IntermediateField.adjoin_union]
  have h1 : Module.finrank ℚ K₁ ≤ 8 * deg x.1 := finrank_adjoin_gens_le x.1
  have h2 : Module.finrank ℚ K₂ ≤ 48 * Module.finrank ℚ K₁ := by
    have := hT3 K₁ hK₁fin hl₁
    norm_num at this
    exact this
  have h5' : Module.finrank ℚ ↥(K₂ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 5)) ≤
      480 * Module.finrank ℚ K₂ := by
    have := hT5 K₂ hK₂fin hl₂
    norm_num at this
    exact this
  change Module.finrank ℚ (fieldOf' x.1) ≤ 552960 * deg x.1
  rw [hF]
  omega

end AbcAdaptation.Tripod
