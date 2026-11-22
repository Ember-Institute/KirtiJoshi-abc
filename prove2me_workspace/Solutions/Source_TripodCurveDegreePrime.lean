/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The iut contributors

Adapted from Iut/Tripod/Galois.lean at 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
-/
import Solutions.Source_TripodCurveNormality
import Solutions.Source_TripodTorsionBasis
import Solutions.Source_TripodTpdGalois
import Mathlib.FieldTheory.Relrank
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut WeierstrassCurve Polynomial
open scoped Classical IntermediateField

private def extendScalarsEquiv {L M' : IntermediateField ℚ Qbar} (h : M' ≤ L) :
    IntermediateField.extendScalars h ≃+* L where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- `[L : M] = [L : M']` for the lift `M' ⊆ ℚ̄` of `M ⊆ L`. -/
private theorem finrank_eq_relfinrank_of_lift_eq {L : IntermediateField ℚ Qbar}
    {M : IntermediateField ℚ L} {M' : IntermediateField ℚ Qbar}
    (hM : IntermediateField.lift M = M') (h : M' ≤ L) :
    Module.finrank M L = IntermediateField.relfinrank M' L := by
  subst hM
  rw [IntermediateField.relfinrank_eq_finrank_of_le h]
  exact Algebra.finrank_eq_of_equiv_equiv (IntermediateField.liftAlgEquiv M).toRingEquiv
    (extendScalarsEquiv h).symm (RingHom.ext fun _ ↦ rfl)

private theorem lift_tpd (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    IntermediateField.lift (tpdC x h3 h5) = fieldOf x.1 := by
  unfold tpdC
  rw [tripodalFieldOf_eq]
  exact IntermediateField.lift_adjoin_simple ℚ (fieldOf' x.1) (gen' x.1)

/-- A positive integer `d < ℓ` is prime to the prime `ℓ`. -/
private theorem coprime_of_pos_of_lt {d ℓ : ℕ} (hℓ : ℓ.Prime) (hd : 0 < d) (h : d < ℓ) :
    Nat.Coprime d ℓ :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun hdvd ↦
    absurd (Nat.le_of_dvd hd hdvd) (not_le.mpr h))

private theorem extendScalars_sup_adjoin (K : IntermediateField ℚ Qbar) (S : Set Qbar) :
    IntermediateField.extendScalars (le_sup_left : K ≤ K ⊔ IntermediateField.adjoin ℚ S) =
      IntermediateField.adjoin K S := by
  apply IntermediateField.restrictScalars_injective ℚ
  change K ⊔ IntermediateField.adjoin ℚ S = _
  exact (IntermediateField.restrictScalars_adjoin_eq_sup ℚ K S).symm

/-- `[K(s) : K] ≤ 2` for `s² ∈ K`. -/
private theorem relfinrank_sup_adjoin_sq_le (K : IntermediateField ℚ Qbar) {s : Qbar} (hs : s ^ 2 ∈ K) :
    IntermediateField.relfinrank K (K ⊔ ℚ⟮s⟯) ≤ 2 := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le le_sup_left, extendScalars_sup_adjoin]
  have hint : IsIntegral K s := (isIntegral s).tower_top
  rw [IntermediateField.adjoin.finrank hint]
  have hmin := minpoly.min K s (monic_X_pow_sub_C (⟨s ^ 2, hs⟩ : K) two_ne_zero) (by simp)
  have := natDegree_le_natDegree hmin
  rwa [natDegree_X_pow_sub_C] at this

/-- **`[K(E_λ[n]) : K]` divides `|GL₂(𝔽_n)| = (n² − 1)(n² − n)`**: it is the index of the
kernel of the mod-`n` representation, the order of its image. -/
private theorem relfinrank_sup_torsion_dvd (K : IntermediateField ℚ Qbar) {l : Qbar} (hl : l ∈ K)
    (n : ℕ) [Fact n.Prime]
    (b : AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n)) :
    IntermediateField.relfinrank K (K ⊔ IntermediateField.adjoin ℚ (torsionCoords l n)) ∣
      (n ^ 2 - 1) * (n ^ 2 - n) := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le le_sup_left, extendScalars_sup_adjoin,
    IntermediateField.finrank_eq_fixingSubgroup_index, ← torsionRep_ker K hl n b,
    Subgroup.index_ker, ← card_GL_two n]
  exact Subgroup.card_subgroup_dvd_card _

private theorem relfinrank_fieldOf_dvd (x : Pt)
    (hpos : IntermediateField.relfinrank (fieldOf x.1) (fieldOf' x.1) ≠ 0) :
    IntermediateField.relfinrank (fieldOf x.1) (fieldOf' x.1) ∣ 184320 := by
  let l := x.1
  let K₀ : IntermediateField ℚ Qbar := fieldOf l
  let K₁ : IntermediateField ℚ Qbar := K₀ ⊔ ℚ⟮sqrtNegOne⟯
  let K₂ : IntermediateField ℚ Qbar := K₁ ⊔ ℚ⟮sqrtLam l⟯
  let K₃ : IntermediateField ℚ Qbar := K₂ ⊔ ℚ⟮sqrtOneSubLam l⟯
  let K₄ : IntermediateField ℚ Qbar := K₃ ⊔ IntermediateField.adjoin ℚ (torsionCoords l 3)
  let K₅ : IntermediateField ℚ Qbar := K₄ ⊔ IntermediateField.adjoin ℚ (torsionCoords l 5)
  have hF : fieldOf' l = K₅ := by
    have hset : ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} : Set Qbar) =
        (({l} ∪ {sqrtNegOne}) ∪ {sqrtLam l}) ∪ {sqrtOneSubLam l} := by
      ext a
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc]
    rw [fieldOf', IntermediateField.adjoin_union, IntermediateField.adjoin_union, hset,
      IntermediateField.adjoin_union, IntermediateField.adjoin_union,
      IntermediateField.adjoin_union]
  have h01 : K₀ ≤ K₁ := le_sup_left
  have h12 : K₁ ≤ K₂ := le_sup_left
  have h23 : K₂ ≤ K₃ := le_sup_left
  have h34 : K₃ ≤ K₄ := le_sup_left
  have h45 : K₄ ≤ K₅ := le_sup_left
  have hprod :
      IntermediateField.relfinrank (fieldOf x.1) (fieldOf' x.1) =
        IntermediateField.relfinrank K₀ K₁ * IntermediateField.relfinrank K₁ K₂ *
        IntermediateField.relfinrank K₂ K₃ * IntermediateField.relfinrank K₃ K₄ *
        IntermediateField.relfinrank K₄ K₅ := by
    change IntermediateField.relfinrank K₀ (fieldOf' l) = _
    rw [hF]
    exact (calc
      IntermediateField.relfinrank K₀ K₁ * IntermediateField.relfinrank K₁ K₂ *
          IntermediateField.relfinrank K₂ K₃ * IntermediateField.relfinrank K₃ K₄ *
          IntermediateField.relfinrank K₄ K₅ =
          IntermediateField.relfinrank K₀ K₂ * IntermediateField.relfinrank K₂ K₃ *
          IntermediateField.relfinrank K₃ K₄ * IntermediateField.relfinrank K₄ K₅ := by
            rw [IntermediateField.relfinrank_mul_relfinrank h01 h12]
      _ = IntermediateField.relfinrank K₀ K₃ * IntermediateField.relfinrank K₃ K₄ *
            IntermediateField.relfinrank K₄ K₅ := by
            rw [IntermediateField.relfinrank_mul_relfinrank (h01.trans h12) h23]
      _ = IntermediateField.relfinrank K₀ K₄ * IntermediateField.relfinrank K₄ K₅ := by
            rw [IntermediateField.relfinrank_mul_relfinrank (h01.trans (h12.trans h23)) h34]
      _ = IntermediateField.relfinrank K₀ K₅ :=
            IntermediateField.relfinrank_mul_relfinrank (h01.trans (h12.trans (h23.trans h34))) h45
      ).symm
  rw [hprod] at hpos ⊢
  simp only [ne_eq, mul_eq_zero, not_or] at hpos
  obtain ⟨⟨⟨⟨hn₁, hn₂⟩, hn₃⟩, _⟩, _⟩ := hpos
  have dvdTwo {n : ℕ} (hn : n ≠ 0) (h : n ≤ 2) : n ∣ 2 := by
    have hn' : n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl <;> decide
  have hl₀ : l ∈ K₀ := IntermediateField.mem_adjoin_simple_self ℚ l
  have hl₁ : l ∈ K₁ := h01 hl₀
  have hl₂ : l ∈ K₂ := h12 hl₁
  have hl₃ : l ∈ K₃ := h23 hl₂
  have hd₁ : IntermediateField.relfinrank K₀ K₁ ∣ 2 :=
    dvdTwo hn₁ (relfinrank_sup_adjoin_sq_le K₀ (s := sqrtNegOne)
      (by rw [sqrtNegOne_sq]; exact neg_mem (one_mem _)))
  have hd₂ : IntermediateField.relfinrank K₁ K₂ ∣ 2 :=
    dvdTwo hn₂ (relfinrank_sup_adjoin_sq_le K₁ (s := sqrtLam l) (by rw [sqrtLam_sq]; exact hl₁))
  have hd₃ : IntermediateField.relfinrank K₂ K₃ ∣ 2 :=
    dvdTwo hn₃ (relfinrank_sup_adjoin_sq_le K₂ (s := sqrtOneSubLam l)
      (by rw [sqrtOneSubLam_sq]; exact sub_mem (one_mem _) hl₂))
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hd₄ : IntermediateField.relfinrank K₃ K₄ ∣ (3 ^ 2 - 1) * (3 ^ 2 - 3) :=
    relfinrank_sup_torsion_dvd K₃ hl₃ 3 (legendre_torsionBasis_three x).some
  have hd₅ : IntermediateField.relfinrank K₄ K₅ ∣ (5 ^ 2 - 1) * (5 ^ 2 - 5) :=
    relfinrank_sup_torsion_dvd K₄ (h34 hl₃) 5 (legendre_torsionBasis_five x).some
  have hd := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hd₁ hd₂) hd₃) hd₄) hd₅
  norm_num at hd
  exact hd

/-- The degree over the tripodal field divides the product of the three quadratic
bounds and the orders of the mod-3 and mod-5 general linear groups. -/
theorem finrank_curveOf_tpd_dvd (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    Module.finrank (tpdC x h3 h5) (curveOf x h3 h5).F ∣ 184320 := by
  haveI : Module.Finite (tpdC x h3 h5) (curveOf x h3 h5).F :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  have hpos : Module.finrank (tpdC x h3 h5) (curveOf x h3 h5).F ≠ 0 :=
    Module.finrank_pos.ne'
  have hle : fieldOf x.1 ≤ fieldOf' x.1 :=
    IntermediateField.adjoin_simple_le_iff.mpr (mem_fieldOfExtended_self x.1)
  have h : Module.finrank (tpdC x h3 h5) (curveOf x h3 h5).F =
      IntermediateField.relfinrank (fieldOf x.1) (fieldOf' x.1) :=
    finrank_eq_relfinrank_of_lift_eq (lift_tpd x h3 h5) hle
  rw [h] at hpos ⊢
  exact relfinrank_fieldOf_dvd x hpos

/-- At a tripod point the Legendre field is Galois over its field of moduli of
degree prime to each prime at least seven. -/
theorem galois_deg_prime (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) :
    IsGaloisOfDegreePrimeTo (curveOf x h3 h5).F (curveOf x h3 h5).E ℓ := by
  refine ⟨isGalois_curveOf_moduli x h3 h5, ?_⟩
  change Nat.Coprime (Module.finrank (modC x h3 h5) (curveOf x h3 h5).F) ℓ
  haveI : Module.Finite (modC x h3 h5) (tpdC x h3 h5) :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : Module.Finite (tpdC x h3 h5) (curveOf x h3 h5).F :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  rw [← Module.finrank_mul_finrank (modC x h3 h5) (tpdC x h3 h5) (curveOf x h3 h5).F]
  have hpos : 0 < Module.finrank (modC x h3 h5) (tpdC x h3 h5) :=
    Module.finrank_pos
  have hsmall := finrank_tpd_le_six x h3 h5
  have h2 : Nat.Coprime 2 ℓ := (Nat.coprime_primes Nat.prime_two hℓ).mpr (by omega)
  have h3' : Nat.Coprime 3 ℓ := (Nat.coprime_primes Nat.prime_three hℓ).mpr (by omega)
  have h5' : Nat.Coprime 5 ℓ := (Nat.coprime_primes Nat.prime_five hℓ).mpr (by omega)
  have hlarge : Nat.Coprime 184320 ℓ := by
    rw [show (184320 : ℕ) = 2 ^ 12 * 3 ^ 2 * 5 by decide]
    exact ((h2.pow_left 12).mul_left (h3'.pow_left 2)).mul_left h5'
  exact Nat.Coprime.mul_left (coprime_of_pos_of_lt hℓ hpos (by omega))
    (hlarge.of_dvd_left (finrank_curveOf_tpd_dvd x h3 h5))

end AbcAdaptation.Tripod
