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
import Definitions.Def_FermatNoncriticalRamificationPositive
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped Classical
open Polynomial
namespace AbcAdaptation.Tripod.Fermat.Proper
namespace QbarPoint
variable {K : Type*} [Field K] [CharZero K] (x : QbarPoint K)
variable {f g : K}
theorem noncritical_eval_mul (hf : f ∈ x.P.1) (hg : g ∈ x.P.1) :
    x.eval (f * g) (x.P.1.mul_mem _ _ hf hg) = x.eval f hf * x.eval g hg := by
  simp only [eval, ← map_mul]
  rfl

theorem noncritical_eval_congr {f g : K} (h : f = g) (hf : f ∈ x.P.1) :
    x.eval f hf = x.eval g (h ▸ hf) := by
  subst h; rfl

theorem noncritical_eval_inv (hf : f ∈ x.P.1) (hfi : f⁻¹ ∈ x.P.1) :
    x.eval f⁻¹ hfi = (x.eval f hf)⁻¹ := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have h0 : ∀ h, x.eval 0 h = 0 := fun _ ↦ x.noncritical_eval_zero
    simp only [inv_zero, h0]
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← x.noncritical_eval_mul hfi hf, x.noncritical_eval_congr (inv_mul_cancel₀ hf0), noncritical_eval_one]

theorem noncritical_eval_aeval {f : K} (hf : f ∈ x.P.1) (p : ℚ[X]) :
    x.eval (aeval f p) (x.P.noncritical_aeval_mem hf p) = aeval (x.eval f hf) p := by
  rw [eval, Place.noncritical_residue_aeval, eval]
  exact (aeval_algHom_apply x.σ.toRatAlgHom _ p).symm

end QbarPoint
namespace NoncriticalP1.ElemMap
@[simp] lemma ramIdx_mob {a b c d : ℚ} (h : a * d - b * c ≠ 0) (z : NoncriticalP1.Pt) :
    (mob a b c d h).ramIdx z = 1 := rfl

@[simp] lemma apply_poly_some {p : ℚ[X]} (hp : 0 < p.natDegree) (z : Tripod.Qbar) :
    (poly p hp).apply (some z) = some (aeval z p) := rfl
lemma apply_mob_none {a b c d : ℚ} (h : a * d - b * c ≠ 0) :
    (mob a b c d h).apply none = if c = 0 then none else some ((a / c : ℚ) : Tripod.Qbar) := rfl

lemma apply_mob_some {a b c d : ℚ} (h : a * d - b * c ≠ 0) (z : Tripod.Qbar) :
    (mob a b c d h).apply (some z) =
      if (c : Tripod.Qbar) * z + d = 0 then none
      else some (((a : Tripod.Qbar) * z + b) / ((c : Tripod.Qbar) * z + d)) := rfl

lemma apply_mob_some_of_ne {a b c d : ℚ} (h : a * d - b * c ≠ 0) {z : Tripod.Qbar}
    (hz : (c : Tripod.Qbar) * z + d ≠ 0) :
    (mob a b c d h).apply (some z) = some (((a : Tripod.Qbar) * z + b) / ((c : Tripod.Qbar) * z + d)) := by
  rw [apply_mob_some, if_neg hz]
lemma one_lt_ramIdx_poly_some_iff {p : ℚ[X]} (hp : 0 < p.natDegree) (z : Tripod.Qbar) :
    1 < (poly p hp).ramIdx (some z) ↔ aeval z (derivative p) = 0 := by
  have hq : (p.map (algebraMap ℚ Tripod.Qbar)) - C (aeval z p) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_sub_C, natDegree_map] at this
    simp at this
    omega
  change 1 < ((p.map (algebraMap ℚ Tripod.Qbar)) - C (aeval z p)).rootMultiplicity z ↔ _
  rw [one_lt_rootMultiplicity_iff_isRoot hq]
  simp [IsRoot, eval_map_algebraMap, derivative_map]

end NoncriticalP1.ElemMap
namespace NoncriticalElementarySource
open NoncriticalP1 (ElemMap)
theorem rootMultiplicity_comp_of_separable {F : Type*} [Field F] {M Q : F[X]} {a b : F}
    (hM : M.Separable) (hb : M.IsRoot b) (hQa : Q.eval a = b) (hQ : Q - C b ≠ 0) :
    (M.comp Q).rootMultiplicity a = (Q - C b).rootMultiplicity a := by
  set R := M /ₘ (X - C b)
  have hMR : (X - C b) * R = M := mul_divByMonic_eq_iff_isRoot.mpr hb
  have hM0 := hM.ne_zero
  have hR0 : R ≠ 0 := by rintro h; rw [h, mul_zero] at hMR; exact hM0 hMR.symm
  have hRb : ¬ R.IsRoot b := by
    intro hRb
    have h1 := rootMultiplicity_le_one_of_separable hM b
    rw [← hMR, rootMultiplicity_mul (by rw [hMR]; exact hM0), rootMultiplicity_X_sub_C_self]
      at h1
    have := (rootMultiplicity_pos hR0).mpr hRb
    omega
  have hRQ : ¬ (R.comp Q).IsRoot a := by
    rwa [IsRoot, eval_comp, hQa]
  have hRQ0 : R.comp Q ≠ 0 := by rintro h; apply hRQ; rw [h]; exact eval_zero
  have hcomp : M.comp Q = (Q - C b) * R.comp Q := by
    rw [← hMR, mul_comp, sub_comp, X_comp, C_comp]
  rw [hcomp, rootMultiplicity_mul (mul_ne_zero hQ hRQ0), rootMultiplicity_eq_zero hRQ, add_zero]

variable {K : Type*} [Field K] [CharZero K] {φ : K}
theorem transcendental_aeval (hφ : Transcendental ℚ φ) {p : ℚ[X]} (hp : 0 < p.natDegree) :
    Transcendental ℚ (aeval φ p) :=
  hφ.aeval p hp.ne' (mem_nonZeroDivisors_of_ne_zero
    (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hp)))
theorem ElemMap.ramIdx_poly_of_natDegree_eq_one {p : ℚ[X]} (hp : 0 < p.natDegree)
    (h1 : p.natDegree = 1) (z : NoncriticalP1.Pt) : (ElemMap.poly p hp).ramIdx z = 1 := by
  cases z with
  | none => exact h1
  | some z =>
    have hq : (p.map (algebraMap ℚ Tripod.Qbar)) - C (aeval z p) ≠ 0 := by
      intro h0
      have := congrArg natDegree h0
      rw [natDegree_sub_C, natDegree_map, natDegree_zero] at this
      omega
    refine le_antisymm (not_lt.mp fun hlt ↦ ?_) ?_
    · have := (ElemMap.one_lt_ramIdx_poly_some_iff hp z).mp hlt
      rw [eq_X_add_C_of_natDegree_le_one h1.le] at this
      simp only [derivative_add, derivative_C_mul_X, derivative_C, add_zero, aeval_C] at this
      have hc : p.coeff 1 ≠ 0 := by
        rw [← h1]; exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hp)
      exact hc ((map_eq_zero_iff _ (algebraMap ℚ Tripod.Qbar).injective).mp this)
    · change 0 < ((p.map (algebraMap ℚ Tripod.Qbar)) - C (aeval z p)).rootMultiplicity z
      rw [rootMultiplicity_pos hq]
      simp [IsRoot, eval_map_algebraMap]
noncomputable def invPt : NoncriticalP1.Pt → NoncriticalP1.Pt
  | none => some 0
  | some a => if a = 0 then none else some a⁻¹
theorem mob_apply_eq_poly {a b d : ℚ} (hdet : a * d - b * 0 ≠ 0)
    (hp : 0 < (C (a / d) * X + C (b / d)).natDegree) (z : NoncriticalP1.Pt) :
    (ElemMap.mob a b 0 d hdet).apply z = (ElemMap.poly _ hp).apply z := by
  have hd : (d : Tripod.Qbar) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hdet
    exact_mod_cast this
  cases z with
  | none => simp [ElemMap.apply_mob_none, ElemMap.apply]
  | some z =>
    rw [ElemMap.apply_mob_some_of_ne _ (by simpa using hd), ElemMap.apply_poly_some]
    simp only [Rat.cast_zero, zero_mul, zero_add, map_add, map_mul, aeval_C, aeval_X,
      eq_ratCast, Rat.cast_div, Option.some.injEq]
    field_simp

/-- A Möbius transformation with `c ≠ 0` is `z ↦ a/c + k/(cz + d)`, `k = (bc - ad)/c`. -/
theorem mob_apply_eq_comp {a b c d : ℚ} (hdet : a * d - b * c ≠ 0) (hc : c ≠ 0)
    (hp₁ : 0 < (C c * X + C d).natDegree)
    (hp₂ : 0 < (C ((b * c - a * d) / c) * X + C (a / c)).natDegree) (z : NoncriticalP1.Pt) :
    (ElemMap.mob a b c d hdet).apply z =
      (ElemMap.poly _ hp₂).apply (invPt ((ElemMap.poly _ hp₁).apply z)) := by
  have hc' : (c : Tripod.Qbar) ≠ 0 := by exact_mod_cast hc
  cases z with
  | none =>
    simp [ElemMap.apply_mob_none, hc, invPt, ElemMap.apply]
  | some z =>
    rw [ElemMap.apply_mob_some, ElemMap.apply_poly_some]
    simp only [map_add, map_mul, aeval_C, aeval_X, eq_ratCast]
    by_cases hz : (c : Tripod.Qbar) * z + d = 0
    · simp [hz, invPt, ElemMap.apply]
    · rw [if_neg hz]
      simp only [invPt, hz, if_false, ElemMap.apply_poly_some, map_add, map_mul, aeval_C,
        aeval_X, eq_ratCast, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Option.some.injEq]
      have hz' : z * (c : Tripod.Qbar) + d ≠ 0 := by rwa [mul_comm]
      field_simp
      ring

variable {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)

/-- Source `ramIdx_of_mem`, transported through the existing order identity. -/
theorem ramIdx_of_mem {φ : M.K} {P : Place M.K} (h : φ ∈ P.1) :
    letI : IsCurveField M.K := M.isCurveField
    ramIdx M hDVR φ P = P.ord (aeval φ (minpoly ℚ (P.residue ⟨φ, h⟩))) := by
  letI : IsCurveField M.K := M.isCurveField
  simp only [ramIdx, dif_pos h, ord_eq_placeOrd]

/-- Source `ramIdx_of_notMem`, for the actual index at every pole. -/
theorem ramIdx_of_notMem {φ : M.K} {P : Place M.K} (h : φ ∉ P.1) :
    letI : IsCurveField M.K := M.isCurveField
    ramIdx M hDVR φ P = -P.ord φ := by
  letI : IsCurveField M.K := M.isCurveField
  simp only [ramIdx, dif_neg h, ord_eq_placeOrd]

/-- Source `val_of_mem`. -/
theorem val_of_mem {φ : M.K} {x : QbarPoint M.K} (h : φ ∈ x.P.1) :
    noncriticalValue M x φ = some (x.eval φ h) := dif_pos h

/-- Source `val_of_notMem`. -/
theorem val_of_notMem {φ : M.K} {x : QbarPoint M.K} (h : φ ∉ x.P.1) :
    noncriticalValue M x φ = none := dif_neg h

/-- The value half of source `inv_spec`, with its exact ramification half supplied
as an explicit child premise. No open theorem module is imported here. -/
theorem inv_spec_of_ramIdx {φ : M.K} (hφ : Transcendental ℚ φ) (x : QbarPoint M.K)
    (hRam : ramIdx M hDVR φ⁻¹ x.P = ramIdx M hDVR φ x.P) :
    noncriticalValue M x φ⁻¹ = invPt (noncriticalValue M x φ) ∧
      ramIdx M hDVR φ⁻¹ x.P = ramIdx M hDVR φ x.P := by
  letI : IsCurveField M.K := M.isCurveField
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ
  have hφi0 : φ⁻¹ ≠ 0 := inv_ne_zero hφ0
  refine ⟨?_, hRam⟩
  rcases lt_trichotomy (x.P.ord φ) 0 with hlt | h0 | hgt
  · have hi : 0 < x.P.ord φ⁻¹ := by rw [x.P.ord_inv]; omega
    rw [val_of_notMem M ((x.P.ord_neg_iff).mp hlt),
      (noncriticalValue_zero_iff M hDVR x hφi0).mpr
        (by simpa only [ord_eq_placeOrd] using hi)]
    rfl
  · obtain ⟨h, hinv⟩ := (x.P.ord_eq_zero_iff hφ0).mp h0
    have ha : x.eval φ h ≠ 0 := by
      rw [Ne, x.noncritical_eval_zero_iff h hφ0]; omega
    rw [val_of_mem M h, val_of_mem M hinv, x.noncritical_eval_inv h hinv]
    simp [invPt, ha]
  · have hi : x.P.ord φ⁻¹ < 0 := by rw [x.P.ord_inv]; omega
    rw [(noncriticalValue_zero_iff M hDVR x hφ0).mpr
        (by simpa only [ord_eq_placeOrd] using hgt),
      val_of_notMem M ((x.P.ord_neg_iff).mp hi)]
    simp [invPt]

end NoncriticalElementarySource
end AbcAdaptation.Tripod.Fermat.Proper
