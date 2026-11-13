import Definitions.Def_FermatNoncriticalElementarySource

section PublishedChildStatements
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalBasic.lean ord_aeval_eq. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtRegularPoint {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : ψ ∈ x.P.1) {g : ℚ[X]} (hg : g ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    x.P.ord (aeval ψ g) = ramIdx M hDVR ψ x.P *
      ((g.map (algebraMap ℚ Tripod.Qbar)).rootMultiplicity (x.eval ψ h) : ℤ) := by
  letI : IsCurveField M.K := M.isCurveField
  sorry

/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalElem.lean ord_aeval_of_notMem. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtPole {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (h : ψ ∉ P.1) {p : ℚ[X]} (hp : p ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    P.ord (aeval ψ p) = p.natDegree * P.ord ψ := by
  letI : IsCurveField M.K := M.isCurveField
  sorry

/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalElem.lean inv_spec second conjunct. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalInverseRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) :
    ramIdx M hDVR ψ⁻¹ x.P = ramIdx M hDVR ψ x.P := by
  letI : IsCurveField M.K := M.isCurveField
  sorry

end PublishedChildStatements

/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of pinned source proofs in
Belyi/CurveField/{Point,NoncriticalBasic,NoncriticalElem}.lean and
Belyi/NoncriticalP1/ElemMap.lean. Commit:
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
See source-consumer.json for exact source boundaries and transformations.
-/

set_option autoImplicit false
open Polynomial
namespace AbcAdaptation.Tripod.Fermat.Proper
namespace NoncriticalElementarySource
open NoncriticalP1 (Pt ElemMap)
variable {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M) {φ : M.K}
theorem poly_spec (hφ : Transcendental ℚ φ) (x : QbarPoint M.K) {p : ℚ[X]}
    (hp : 0 < p.natDegree) :
    noncriticalValue M x (aeval φ p) = (ElemMap.poly p hp).apply (noncriticalValue M x φ) ∧
      ramIdx M hDVR (aeval φ p) x.P = ramIdx M hDVR φ x.P * (ElemMap.poly p hp).ramIdx (noncriticalValue M x φ) := by
  letI : IsCurveField M.K := M.isCurveField
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hp
  by_cases h : φ ∈ x.P.1
  · have h' := x.P.noncritical_aeval_mem h p
    have hev := x.noncritical_eval_aeval h p
    rw [val_of_mem M h, val_of_mem M h', hev]
    refine ⟨rfl, ?_⟩
    set m := minpoly ℚ (x.P.residue ⟨aeval φ p, h'⟩)
    have hr := x.P.noncritical_isIntegral_residue ⟨aeval φ p, h'⟩
    have hm0 : m ≠ 0 := minpoly.ne_zero hr
    have hcomp0 : m.comp p ≠ 0 := by
      rw [Ne, comp_eq_zero_iff, not_or]
      refine ⟨hm0, fun ⟨_, h2⟩ ↦ ?_⟩
      have := congrArg natDegree h2
      rw [natDegree_C] at this
      omega
    rw [ramIdx_of_mem M hDVR h', ← aeval_comp, noncriticalPolynomialOrderAtRegularPoint M hDVR φ hφ x h hcomp0, Polynomial.map_comp]
    congr 2
    refine rootMultiplicity_comp_of_separable ((minpoly.irreducible hr).separable.map) ?_
      (by rw [eval_map_algebraMap]) ?_
    · rw [IsRoot, eval_map_algebraMap, ← hev]
      exact (aeval_algHom_apply x.σ.toRatAlgHom _ m).trans (by
        simp [m, minpoly.aeval])
    · intro h0
      have := congrArg natDegree h0
      rw [natDegree_sub_C, natDegree_map, natDegree_zero] at this
      omega
  · have hord := noncriticalPolynomialOrderAtPole M hDVR φ hφ x.P h hp0
    have hneg := (x.P.ord_neg_iff).mpr h
    have h' : aeval φ p ∉ x.P.1 := by
      rw [← x.P.ord_neg_iff, hord]
      exact mul_neg_of_pos_of_neg (by exact_mod_cast hp) hneg
    rw [val_of_notMem M h, val_of_notMem M h', ramIdx_of_notMem M hDVR h', ramIdx_of_notMem M hDVR h, hord]
    refine ⟨rfl, ?_⟩
    change _ = _ * (p.natDegree : ℤ)
    ring

theorem mob_spec (hφ : Transcendental ℚ φ) (x : QbarPoint M.K) {a b c d : ℚ}
    (hdet : a * d - b * c ≠ 0) :
    Transcendental ℚ (NoncriticalP1.applyK (.mob a b c d hdet) φ) ∧
      noncriticalValue M x (NoncriticalP1.applyK (.mob a b c d hdet) φ) = (ElemMap.mob a b c d hdet).apply (noncriticalValue M x φ) ∧
      ramIdx M hDVR (NoncriticalP1.applyK (.mob a b c d hdet) φ) x.P = ramIdx M hDVR φ x.P := by
  letI : IsCurveField M.K := M.isCurveField
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := by rintro rfl; simp at hdet
    have ha : a / d ≠ 0 := div_ne_zero (by rintro rfl; simp at hdet) hd
    have hp1 : (C (a / d) * X + C (b / d)).natDegree = 1 := natDegree_linear ha
    have hp : 0 < (C (a / d) * X + C (b / d)).natDegree := by omega
    have heq : NoncriticalP1.applyK (.mob a b 0 d hdet) φ = aeval φ (C (a / d) * X + C (b / d)) := by
      have hd' : (d : M.K) ≠ 0 := by exact_mod_cast hd
      simp only [NoncriticalP1.applyK, map_add, map_mul, aeval_C, aeval_X, eq_ratCast, Rat.cast_div,
        Rat.cast_zero, zero_mul, zero_add]
      field_simp
    obtain ⟨hv, he⟩ := poly_spec M hDVR hφ x hp
    rw [heq, hv, he, ElemMap.ramIdx_poly_of_natDegree_eq_one hp hp1, Nat.cast_one, mul_one,
      mob_apply_eq_poly hdet hp]
    exact ⟨transcendental_aeval hφ hp, rfl, rfl⟩
  · have hk : (b * c - a * d) / c ≠ 0 :=
      div_ne_zero (fun h ↦ hdet (by linear_combination -h)) hc
    have hp₁1 : (C c * X + C d).natDegree = 1 := natDegree_linear hc
    have hp₂1 : (C ((b * c - a * d) / c) * X + C (a / c)).natDegree = 1 := natDegree_linear hk
    have hp₁ : 0 < (C c * X + C d).natDegree := by omega
    have hp₂ : 0 < (C ((b * c - a * d) / c) * X + C (a / c)).natDegree := by omega
    have hφ₁ := transcendental_aeval hφ hp₁
    have hφ₂ := transcendental_inv hφ₁
    have hden : (c : M.K) * φ + d ≠ 0 := by
      have := ne_zero_of_transcendental hφ₁
      simpa using this
    have heq : NoncriticalP1.applyK (.mob a b c d hdet) φ =
        aeval (aeval φ (C c * X + C d))⁻¹ (C ((b * c - a * d) / c) * X + C (a / c)) := by
      have hc' : (c : M.K) ≠ 0 := by exact_mod_cast hc
      simp only [NoncriticalP1.applyK, map_add, map_mul, aeval_C, aeval_X, eq_ratCast, Rat.cast_div,
        Rat.cast_sub, Rat.cast_mul]
      have hden' : φ * (c : M.K) + d ≠ 0 := by rwa [mul_comm]
      field_simp
      ring
    obtain ⟨hv₁, he₁⟩ := poly_spec M hDVR hφ x hp₁
    obtain ⟨hv₂, he₂⟩ := inv_spec_of_ramIdx M hDVR hφ₁ x
      (noncriticalInverseRamification M hDVR _ hφ₁ x)
    obtain ⟨hv₃, he₃⟩ := poly_spec M hDVR hφ₂ x hp₂
    rw [heq, hv₃, he₃, hv₂, he₂, hv₁, he₁, ElemMap.ramIdx_poly_of_natDegree_eq_one hp₁ hp₁1,
      ElemMap.ramIdx_poly_of_natDegree_eq_one hp₂ hp₂1, mob_apply_eq_comp hdet hc hp₁ hp₂]
    exact ⟨transcendental_aeval hφ₂ hp₂, rfl, by simp⟩

end NoncriticalElementarySource
end AbcAdaptation.Tripod.Fermat.Proper

open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper
open AbcAdaptation.Tripod.Fermat.Proper.NoncriticalElementarySource
open AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1

theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : NoncriticalP1.ElemMap) :
    Transcendental ℚ (NoncriticalP1.applyK h ψ) ∧
    noncriticalValue M x (NoncriticalP1.applyK h ψ) = h.apply (noncriticalValue M x ψ) ∧
    ramIdx M hDVR (NoncriticalP1.applyK h ψ) x.P =
      ramIdx M hDVR ψ x.P * (h.ramIdx (noncriticalValue M x ψ) : ℤ) := by
  cases h with
  | mob a b c d hdet =>
    obtain ⟨h1, h2, h3⟩ := NoncriticalElementarySource.mob_spec M hDVR hψ x hdet
    exact ⟨h1, h2, by rw [h3, NoncriticalP1.ElemMap.ramIdx_mob, Nat.cast_one, mul_one]⟩
  | poly p hp =>
    obtain ⟨h2, h3⟩ := NoncriticalElementarySource.poly_spec M hDVR hψ x hp
    exact ⟨NoncriticalElementarySource.transcendental_aeval hψ hp, h2, h3⟩

#print axioms solution
