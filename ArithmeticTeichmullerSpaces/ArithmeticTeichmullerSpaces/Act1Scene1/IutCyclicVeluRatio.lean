/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Tripod/CyclicPoints.lean` and
`refer/iut/Iut/Tripod/CyclicIsogeny.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `c35ca616ba5ec707d8ef08a781df35fadba16532`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: extracts the nonzero ratio and Galois reindexing proofs; adapts
coordinate helpers to Mathlib and proves descent directly in the algebraic closure.
The resulting nonzero element supplies the number-field product formula.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutModEllRepCyclicSubgroup
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
source-id: IUT-COR312-CYCLIC-VELU-RATIO
fidelity: a Galois-stable subgroup of odd order and two rational pairs of
points T, R with T nonzero, 2T = 0 and 2R = T give a nonzero product of
Vélu ratios in the base number field. The number-field product formula
consumes this element. Rationality of the four points is explicit; six-torsion
rationality in InitialThetaData does not supply rational halves of two-torsion.
Local and archimedean estimates and the no-cyclic-subgroup bound remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutCyclicVelu

open WeierstrassCurve WeierstrassCurve.Affine NumberField
open scoped Classical

noncomputable section

section Ratio

variable {L : Type*} [Field L] {W : WeierstrassCurve L}
variable [DecidableEq L]

/-- The affine x coordinate, with value zero at the origin. -/
def xCoordinate : W.toAffine.Point → L
  | .zero => 0
  | .some x _ _ => x

@[simp] lemma xCoordinate_zero : xCoordinate (0 : W.toAffine.Point) = 0 := rfl

/-- Equal x coordinates of nonzero points determine the point up to sign. -/
lemma eq_or_eq_neg_of_xCoordinate_eq {P Q : W.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : xCoordinate P = xCoordinate Q) : P = Q ∨ P = -Q := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x', y', h'⟩
  · exact absurd rfl hQ
  exact (Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hx

variable (H : AddSubgroup W.toAffine.Point) [Fintype H]

/-- The nonzero points of a finite subgroup. -/
def nonzeroPoints : Finset H := Finset.univ.filter (fun Q => Q ≠ 0)

lemma mem_nonzeroPoints {Q : H} : Q ∈ nonzeroPoints H ↔ Q ≠ 0 := by
  simp [nonzeroPoints]

/-- A point outside a subgroup has a different x coordinate from its nonzero points. -/
lemma xCoordinate_ne_of_notMem {P Q : W.toAffine.Point}
    (hP : P ∉ H) (hQ : Q ∈ H) (hQ0 : Q ≠ 0) : xCoordinate P ≠ xCoordinate Q := by
  have hP0 : P ≠ 0 := fun h => hP (h ▸ H.zero_mem)
  intro hx
  rcases eq_or_eq_neg_of_xCoordinate_eq hP0 hQ0 hx with h | h
  · exact hP (h ▸ hQ)
  · exact hP (h ▸ H.neg_mem hQ)

/-- An element of a subgroup of odd order with `2Q = 0` is zero. -/
lemma eq_zero_of_add_self {Q : W.toAffine.Point} (hodd : Odd (Fintype.card H)) (hQ : Q ∈ H)
    (h2 : Q + Q = 0) : Q = 0 := by
  obtain ⟨k, hk⟩ := hodd
  have hcard : (Fintype.card H) • (⟨Q, hQ⟩ : H) = 0 := card_nsmul_eq_zero
  have hcard' : (Fintype.card H) • Q = 0 := by
    have := congrArg Subtype.val hcard
    rwa [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero] at this
  have hkQ : k • Q + k • Q = 0 := by rw [← add_nsmul, ← two_mul, mul_nsmul, two_nsmul, h2,
    nsmul_zero]
  rw [hk, add_nsmul, one_nsmul, mul_comm, mul_nsmul, two_nsmul, hkQ, zero_add] at hcard'
  exact hcard'

/-- A point of order `2` is not in a subgroup of odd order. -/
lemma notMem_of_add_self (hodd : Odd (Fintype.card H)) {T : W.toAffine.Point} (hT0 : T ≠ 0)
    (hT2 : T + T = 0) : T ∉ H := fun hT => hT0 (eq_zero_of_add_self H hodd hT hT2)

/-- **The Vélu ratio** `∏_{Q ∈ H∖0} (x(T) − x(R + Q))/(x(T) − x(Q))`. -/
noncomputable def veluRatio (T R : W.toAffine.Point) : L :=
  ∏ Q ∈ nonzeroPoints H, (xCoordinate T - xCoordinate (R + (Q : W.toAffine.Point))) / (xCoordinate T - xCoordinate (Q : W.toAffine.Point))

variable {H}

/-- The Vélu ratio is nonzero for `T` of order `2` and `2R = T`. -/
lemma veluRatio_ne_zero (hodd : Odd (Fintype.card H)) {T R : W.toAffine.Point} (hT0 : T ≠ 0)
    (hT2 : T + T = 0) (hRT : R + R = T) : veluRatio H T R ≠ 0 := by
  have hT : T ∉ H := notMem_of_add_self H hodd hT0 hT2
  have hR : R ∉ H := fun hR => hT (hRT ▸ H.add_mem hR hR)
  refine Finset.prod_ne_zero_iff.mpr fun Q hQ => div_ne_zero ?_ ?_
  · rw [sub_ne_zero]
    intro hx
    have hRQ : R + (Q : W.toAffine.Point) ≠ 0 := fun h =>
      hR (by rw [eq_neg_of_add_eq_zero_left h]; exact H.neg_mem Q.2)
    have hTR : T - R = R := by rw [← hRT]; abel
    rcases eq_or_eq_neg_of_xCoordinate_eq hT0 hRQ hx with h | h
    · apply hR
      have : (Q : W.toAffine.Point) = R := by rw [← hTR, h]; abel
      exact this ▸ Q.2
    · apply hR
      have hTT : -T = T := neg_eq_of_add_eq_zero_left hT2
      have : (Q : W.toAffine.Point) = R := by
        rw [← hTR, ← hTT, h]; abel
      exact this ▸ Q.2
  · exact sub_ne_zero.mpr (xCoordinate_ne_of_notMem H hT Q.2 fun h =>
      (mem_nonzeroPoints H).mp hQ (Subtype.ext h))

end Ratio

section Descent

universe u
variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

/-- Coordinates commute with the actual Galois action. -/
lemma xCoordinate_galPointMap (σ : Fbar ≃ₐ[F] Fbar)
    (Q : Affine.Point (Affine.baseChange E Fbar)) :
    xCoordinate (JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q) =
      σ (xCoordinate Q) := by
  rcases Q with _ | ⟨a, b, h⟩
  · change 0 = σ 0
    exact (map_zero σ).symm
  · rfl

/-- Every point obtained from the base field is fixed by Galois. -/
lemma galPointMap_baseChange (σ : Fbar ≃ₐ[F] Fbar) (Q : Affine.Point (Affine.baseChange E F)) :
    JoshiTeich.ReferenceIut.galPointMap F E Fbar σ
      (Affine.Point.baseChange (W' := E) F Fbar Q) = Affine.Point.baseChange (W' := E) F Fbar Q :=
  Affine.Point.map_baseChange (W' := E) σ.toAlgHom Q

variable {E Fbar}
variable {H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar))} [Fintype H]

/-- A stable subgroup gives a Galois-invariant ratio for fixed points T and R. -/
lemma veluRatio_galois
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H)
    (σ : Fbar ≃ₐ[F] Fbar) {T R : Affine.Point (Affine.baseChange E Fbar)}
    (hT : JoshiTeich.ReferenceIut.galPointMap F E Fbar σ T = T)
    (hR : JoshiTeich.ReferenceIut.galPointMap F E Fbar σ R = R) :
    σ (veluRatio H T R) = veluRatio H T R := by
  set g := JoshiTeich.ReferenceIut.galPointMap F E Fbar σ
  set g' := JoshiTeich.ReferenceIut.galPointMap F E Fbar σ.symm
  have hgg' : ∀ Q, g (g' Q) = Q := by
    rintro (_ | ⟨a, b, h⟩)
    · rfl
    · change Affine.Point.some (σ (σ.symm a)) (σ (σ.symm b)) _ = _
      congr 1 <;> simp
  have hg'g : ∀ Q, g' (g Q) = Q := by
    rintro (_ | ⟨a, b, h⟩)
    · rfl
    · change Affine.Point.some (σ.symm (σ a)) (σ.symm (σ b)) _ = _
      congr 1 <;> simp
  unfold veluRatio
  rw [map_prod]
  refine Finset.prod_nbij' (fun Q => ⟨g Q, hgal σ Q.1 Q.2⟩)
    (fun Q => ⟨g' Q, hgal σ.symm Q.1 Q.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    rw [mem_nonzeroPoints] at hQ ⊢
    intro h
    apply hQ
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at this ⊢
    rw [← hg'g Q, this, map_zero]
  · intro Q hQ
    rw [mem_nonzeroPoints] at hQ ⊢
    intro h
    apply hQ
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at this ⊢
    rw [← hgg' Q, this, map_zero]
  · intro Q _; exact Subtype.ext (hg'g Q)
  · intro Q _; exact Subtype.ext (hgg' Q)
  · intro Q _
    rw [map_div₀, map_sub, map_sub, ← xCoordinate_galPointMap, ← xCoordinate_galPointMap,
      ← xCoordinate_galPointMap, map_add, hT, hR]

/-- The product of two ratios for rational point pairs descends to the base field. -/
lemma exists_algebraMap_eq_ratio
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H)
    (T₁ R₁ T₂ R₂ : Affine.Point (Affine.baseChange E F)) :
    ∃ ρ : F, algebraMap F Fbar ρ =
      veluRatio H (Affine.Point.baseChange (W' := E) F Fbar T₁) (Affine.Point.baseChange (W' := E) F Fbar R₁) *
        veluRatio H (Affine.Point.baseChange (W' := E) F Fbar T₂) (Affine.Point.baseChange (W' := E) F Fbar R₂) := by
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  rw [map_mul,
    veluRatio_galois hgal σ (galPointMap_baseChange E Fbar σ T₁)
      (galPointMap_baseChange E Fbar σ R₁),
    veluRatio_galois hgal σ (galPointMap_baseChange E Fbar σ T₂)
      (galPointMap_baseChange E Fbar σ R₂)]

/-- Rational two-torsion points and their rational halves give a nonzero product-formula input. -/
theorem exists_nonzero_ratio_productFormula
    (hodd : Odd (Fintype.card H))
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H)
    (T₁ R₁ T₂ R₂ : Affine.Point (Affine.baseChange E F))
    (hT₁0 : T₁ ≠ 0) (hT₁2 : T₁ + T₁ = 0) (hR₁ : R₁ + R₁ = T₁)
    (hT₂0 : T₂ ≠ 0) (hT₂2 : T₂ + T₂ = 0) (hR₂ : R₂ + R₂ = T₂) :
    ∃ ρ : F, ρ ≠ 0 ∧
      algebraMap F Fbar ρ =
        veluRatio H (Affine.Point.baseChange (W' := E) F Fbar T₁) (Affine.Point.baseChange (W' := E) F Fbar R₁) *
          veluRatio H (Affine.Point.baseChange (W' := E) F Fbar T₂) (Affine.Point.baseChange (W' := E) F Fbar R₂) ∧
      (∏ w : InfinitePlace F, (w ρ) ^ w.mult) * ∏ᶠ w : FinitePlace F, w ρ = 1 := by
  obtain ⟨ρ, hρ⟩ := exists_algebraMap_eq_ratio hgal T₁ R₁ T₂ R₂
  let b := Affine.Point.baseChange (W' := E) F Fbar
  have hb : Function.Injective b := Affine.Point.map_injective (Algebra.ofId F Fbar)
  have hp (T R : Affine.Point (Affine.baseChange E F)) (hT0 : T ≠ 0) (hT2 : T + T = 0)
      (hR : R + R = T) : veluRatio H (b T) (b R) ≠ 0 := by
    apply veluRatio_ne_zero hodd
    · intro h
      exact hT0 (hb (h.trans (map_zero b).symm))
    · rw [← map_add, hT2, map_zero]
    · rw [← map_add, hR]
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, map_zero] at hρ
    exact (mul_ne_zero (hp T₁ R₁ hT₁0 hT₁2 hR₁) (hp T₂ R₂ hT₂0 hT₂2 hR₂)) hρ.symm
  exact ⟨ρ, hρ0, hρ, NumberField.prod_abs_eq_one hρ0⟩

/-- The logarithmic product formula over any finite set containing the finite support. -/
lemma logProductFormula {ρ : F} (hρ0 : ρ ≠ 0) (S : Finset (FinitePlace F))
    (hS : ∀ w : FinitePlace F, w ρ ≠ 1 → w ∈ S) :
    (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w ρ)) +
      ∑ w ∈ S, Real.log (w ρ) = 0 := by
  have hpf := NumberField.prod_abs_eq_one hρ0
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun w hw => hS w hw] at hpf
  have hw : ∀ w : InfinitePlace F, 0 < w ρ := fun w => w.pos_iff.mpr hρ0
  have hv : ∀ w : FinitePlace F, 0 < w ρ := fun w => FinitePlace.pos_iff.mpr hρ0
  have := congrArg Real.log hpf
  rw [Real.log_one, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun w _ => (pow_pos (hw w) _).ne')
    (Finset.prod_ne_zero_iff.mpr fun w _ => (hv w).ne'),
    Real.log_prod (fun w _ => (pow_pos (hw w) _).ne'),
    Real.log_prod (fun w _ => (hv w).ne')] at this
  simpa only [Real.log_pow] using this

/-- A cyclic subgroup and rational point pairs supply the logarithmic product formula. -/
theorem exists_ratio_logProductFormula
    (hodd : Odd (Fintype.card H))
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H)
    (T₁ R₁ T₂ R₂ : Affine.Point (Affine.baseChange E F))
    (hT₁0 : T₁ ≠ 0) (hT₁2 : T₁ + T₁ = 0) (hR₁ : R₁ + R₁ = T₁)
    (hT₂0 : T₂ ≠ 0) (hT₂2 : T₂ + T₂ = 0) (hR₂ : R₂ + R₂ = T₂) :
    ∃ ρ : F, ρ ≠ 0 ∧
      algebraMap F Fbar ρ =
        veluRatio H (Affine.Point.baseChange (W' := E) F Fbar T₁) (Affine.Point.baseChange (W' := E) F Fbar R₁) *
          veluRatio H (Affine.Point.baseChange (W' := E) F Fbar T₂) (Affine.Point.baseChange (W' := E) F Fbar R₂) ∧
      ∀ S : Finset (FinitePlace F), (∀ w : FinitePlace F, w ρ ≠ 1 → w ∈ S) →
        (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w ρ)) +
          ∑ w ∈ S, Real.log (w ρ) = 0 := by
  obtain ⟨ρ, hρ0, hρ, _⟩ := exists_nonzero_ratio_productFormula hodd hgal
    T₁ R₁ T₂ R₂ hT₁0 hT₁2 hR₁ hT₂0 hT₂2 hR₂
  exact ⟨ρ, hρ0, hρ, fun S hS => logProductFormula hρ0 S hS⟩

end Descent

end
end JoshiTeich.Act1Scene1.IutCyclicVelu
