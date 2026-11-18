/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths: Iut/Anabelian/TateTorsion.lean and Iut/Cor312/ThetaData/TateStructure.lean
TateTorsion.lean source commit: 76c7866b5bbc4adbd245a30af1a4fd05d32f8c3f (Christian Merten)
Adaptation: use the existing Tate structure and graph line in the adaptation namespace.
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.Basic
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateStructure

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.TateStructure

open WeierstrassCurve TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} (S : TateStructure E)

lemma ofUnit_eq_iff (u v : kˣ) :
    S.ofUnit u = S.ofUnit v ↔ ∃ n : ℤ, v = S.t.q ^ n * u := by
  unfold ofUnit
  rw [S.iso.injective.eq_iff, Additive.ofMul.injective.eq_iff, QuotientGroup.eq]
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, mul_comm, mul_inv_cancel_left]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, mul_comm (S.t.q ^ n) u, inv_mul_cancel_left]⟩

lemma ofUnit_surjective : Function.Surjective S.ofUnit := fun P => by
  obtain ⟨a, ha⟩ := S.iso.surjective P
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  exact ⟨u, by unfold ofUnit; rw [hu]; simpa using ha⟩

lemma q_zpow_injective : Function.Injective (fun n : ℤ => S.t.q ^ n) := by
  intro a b h
  have hnorm := congrArg (fun x : kˣ => ‖(x : k)‖) h
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow, norm_zpow] at hnorm
  exact zpow_right_injective₀ S.t.norm_q_pos S.t.norm_lt_one.ne hnorm

lemma ofUnit_eq_zero_iff (u : kˣ) : S.ofUnit u = 0 ↔ ∃ n : ℤ, u = S.t.q ^ n := by
  rw [← S.ofUnit_one, S.ofUnit_eq_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right hn.symm
  · rintro ⟨n, rfl⟩
    exact ⟨-n, by rw [zpow_neg, inv_mul_cancel]⟩

lemma nsmul_ofUnit (n : ℕ) (u : kˣ) : n • S.ofUnit u = S.ofUnit (u ^ n) := by
  unfold ofUnit
  rw [← map_nsmul]
  rfl

lemma ofUnit_mem_torsionBy_iff (ℓ : ℕ) (u : kˣ) :
    S.ofUnit u ∈ AddSubgroup.torsionBy E.toAffine.Point ℓ ↔ ∃ n : ℤ, u ^ ℓ = S.t.q ^ n := by
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_ofUnit, ofUnit_eq_zero_iff]

lemma expo_congr (ℓ : ℕ) {u v : kˣ} {n m : ℤ} (huv : S.ofUnit u = S.ofUnit v)
    (hu : u ^ ℓ = S.t.q ^ n) (hv : v ^ ℓ = S.t.q ^ m) : (m : ZMod ℓ) = n := by
  obtain ⟨j, hj⟩ := (S.ofUnit_eq_iff u v).mp huv
  have h : S.t.q ^ m = S.t.q ^ (j * ℓ + n) := by
    rw [← hv, hj, mul_pow, hu, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  have hm := S.q_zpow_injective h
  simp [hm, Int.cast_add, Int.cast_mul]

variable (ℓ : ℕ)

/-- The ℓ-torsion of `E(k)`. -/
abbrev torsion (E : WeierstrassCurve k) : AddSubgroup E.toAffine.Point :=
  AddSubgroup.torsionBy E.toAffine.Point ℓ

lemma exists_rep (P : ↥(torsion ℓ E)) :
    ∃ u : kˣ, S.ofUnit u = P ∧ ∃ n : ℤ, u ^ ℓ = S.t.q ^ n := by
  obtain ⟨u, hu⟩ := S.ofUnit_surjective P.1
  exact ⟨u, hu, (S.ofUnit_mem_torsionBy_iff ℓ u).mp (hu ▸ P.2)⟩

def rep (P : ↥(torsion ℓ E)) : kˣ := (S.exists_rep ℓ P).choose

lemma ofUnit_rep (P : ↥(torsion ℓ E)) : S.ofUnit (S.rep ℓ P) = P :=
  (S.exists_rep ℓ P).choose_spec.1

def expo (P : ↥(torsion ℓ E)) : ℤ := (S.exists_rep ℓ P).choose_spec.2.choose

lemma rep_pow (P : ↥(torsion ℓ E)) : S.rep ℓ P ^ ℓ = S.t.q ^ S.expo ℓ P :=
  (S.exists_rep ℓ P).choose_spec.2.choose_spec

/-- The residue homomorphism sends the class of `u` to `n` modulo `ℓ` when `u ^ ℓ = q ^ n`. -/
def resid : ↥(torsion ℓ E) →+ ZMod ℓ where
  toFun P := (S.expo ℓ P : ZMod ℓ)
  map_zero' := by
    obtain ⟨j, hj⟩ := (S.ofUnit_eq_zero_iff _).mp (S.ofUnit_rep ℓ 0)
    have h : S.t.q ^ S.expo ℓ 0 = S.t.q ^ (j * ℓ) := by
      rw [← S.rep_pow, hj, ← zpow_natCast, ← zpow_mul]
    have := S.q_zpow_injective h
    simp [this]
  map_add' P Q := by
    have h : S.ofUnit (S.rep ℓ (P + Q)) = S.ofUnit (S.rep ℓ P * S.rep ℓ Q) := by
      rw [ofUnit_mul, ofUnit_rep, ofUnit_rep, ofUnit_rep]
      rfl
    have := S.expo_congr ℓ h (S.rep_pow ℓ (P + Q))
      (by rw [mul_pow, rep_pow, rep_pow, ← zpow_add])
    simp only [Int.cast_add] at this
    exact this.symm

lemma resid_apply (P : ↥(torsion ℓ E)) : S.resid ℓ P = (S.expo ℓ P : ZMod ℓ) := rfl

lemma resid_eq_zero_iff (P : ↥(torsion ℓ E)) :
    S.resid ℓ P = 0 ↔ (P : E.toAffine.Point) ∈ S.graphLine ℓ := by
  constructor
  · intro h
    rw [resid_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨j, hj⟩ := h
    refine ⟨S.rep ℓ P * (S.t.q ^ j)⁻¹, ?_, ?_⟩
    · rw [mul_pow, rep_pow, hj, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm (j : ℤ),
        mul_inv_cancel]
    · rw [ofUnit_mul, ofUnit_rep, (S.ofUnit_eq_zero_iff (S.t.q ^ j)⁻¹).mpr ⟨-j, by rw [zpow_neg]⟩,
        add_zero]
  · rintro ⟨ζ, hζ, hζP⟩
    have := S.expo_congr ℓ (hζP.trans (S.ofUnit_rep ℓ P).symm) (by rw [hζ, zpow_zero])
      (S.rep_pow ℓ P)
    rw [resid_apply, this]
    simp

variable [NeZero ℓ]

lemma graphLine_le_torsion : S.graphLine ℓ ≤ torsion ℓ E := by
  rintro _ ⟨ζ, hζ, rfl⟩
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_ofUnit, hζ, ofUnit_one]

lemma ofUnit_rootsOfUnity_surjective :
    Function.Surjective (fun ζ : rootsOfUnity ℓ k =>
      (⟨S.ofUnit ζ.1, ⟨ζ.1, (mem_rootsOfUnity ℓ ζ.1).mp ζ.2, rfl⟩⟩ : ↥(S.graphLine ℓ))) := by
  rintro ⟨P, ζ, hζ, rfl⟩
  exact ⟨⟨ζ, (mem_rootsOfUnity ℓ ζ).mpr hζ⟩, rfl⟩

instance finite_graphLine : Finite ↥(S.graphLine ℓ) :=
  Finite.of_surjective _ (S.ofUnit_rootsOfUnity_surjective ℓ)

lemma card_graphLine_le : Nat.card ↥(S.graphLine ℓ) ≤ ℓ :=
  (Nat.card_le_card_of_surjective _ (S.ofUnit_rootsOfUnity_surjective ℓ)).trans
    (card_rootsOfUnity (R := k) (k := ℓ))

lemma resid_ker : (S.resid ℓ).ker = (S.graphLine ℓ).addSubgroupOf (torsion ℓ E) := by
  ext P
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, resid_eq_zero_iff]

lemma card_torsion_eq :
    Nat.card ↥(torsion ℓ E) = Nat.card ↥(S.graphLine ℓ) * Nat.card ↥(S.resid ℓ).range := by
  rw [← AddSubgroup.card_mul_index (S.resid ℓ).ker, AddSubgroup.index_ker, resid_ker]
  rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (S.graphLine_le_torsion ℓ)).toEquiv]

lemma card_range_le : Nat.card ↥(S.resid ℓ).range ≤ ℓ :=
  (Nat.card_le_card_of_injective _ Subtype.val_injective).trans (by rw [Nat.card_zmod])

include S in
/-- The ℓ-torsion of a Tate curve has at most `ℓ²` elements. -/
lemma card_torsion_le : Nat.card ↥(torsion ℓ E) ≤ ℓ * ℓ := by
  rw [S.card_torsion_eq ℓ]
  exact Nat.mul_le_mul (S.card_graphLine_le ℓ) (S.card_range_le ℓ)

include S in
theorem finite_torsion : Finite ↥(torsion ℓ E) := by
  apply Nat.finite_of_card_ne_zero
  rw [S.card_torsion_eq ℓ]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

lemma resid_range_eq_top (hcard : ℓ * ℓ ≤ Nat.card ↥(torsion ℓ E)) :
    (S.resid ℓ).range = ⊤ := by
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmod]
  apply Nat.le_antisymm (S.card_range_le ℓ)
  apply Nat.le_of_not_gt
  intro hlt
  have hUpper : Nat.card ↥(torsion ℓ E) < ℓ * ℓ := calc
    Nat.card ↥(torsion ℓ E) = Nat.card ↥(S.graphLine ℓ) * Nat.card ↥(S.resid ℓ).range :=
      S.card_torsion_eq ℓ
    _ ≤ ℓ * Nat.card ↥(S.resid ℓ).range := Nat.mul_le_mul_right _ (S.card_graphLine_le ℓ)
    _ < ℓ * ℓ := (Nat.mul_lt_mul_left (NeZero.pos ℓ)).2 hlt
  exact (Nat.not_lt_of_ge hcard) hUpper

/-- If the ℓ-torsion has `ℓ²` elements, `q` has an ℓ-th root modulo `q^{ℓℤ}`. -/
lemma exists_root_class (hcard : ℓ * ℓ ≤ Nat.card ↥(torsion ℓ E)) :
    ∃ u : kˣ, ∃ m : ℤ, u ^ ℓ = S.t.q ^ (1 + (ℓ : ℤ) * m) := by
  have hOne : (1 : ZMod ℓ) ∈ (S.resid ℓ).range := by
    rw [S.resid_range_eq_top ℓ hcard]
    trivial
  obtain ⟨P, hP⟩ := hOne
  rw [resid_apply, ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at hP
  obtain ⟨m, hm⟩ := hP
  refine ⟨S.rep ℓ P, m, ?_⟩
  rw [S.rep_pow, ← hm, add_comm 1 (S.expo ℓ P - 1), sub_add_cancel]

end

end AbcAdaptation.Reference.Iut.TateStructure
