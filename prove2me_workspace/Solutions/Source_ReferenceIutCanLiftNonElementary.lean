/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as stated in the upstream source header.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.Index
import Solutions.Source_ReferenceIutCanLiftFrickeComplexAction
import Solutions.Source_ReferenceIutCanLiftPointMaps

set_option autoImplicit false

/-!
# Non-elementarity of projective actions

A finite-index subgroup contains positive powers of the commutator and its conjugate.
Their projective actions have distinct fixed points when a generator moves infinity.
-/

open OnePoint
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

section ProjectiveAction

variable {k : Type*} [NontriviallyNormedField k] [DecidableEq k]
  {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k}

lemma actsOn_slMap (σ : ℝ →+* k) (Γ : Subgroup SL(2, ℝ)) : ActsOn Γ (slMap σ) :=
  fun g _ h _ y ↦ by rw [slMap_mul, mul_smul]

lemma ActsOn.smul_pow (hact : ActsOn Γ a) {g : SL(2, ℝ)} (hg : g ∈ Γ) (n : ℕ)
    (y : OnePoint k) : a (g ^ n) • y = (fun w ↦ a g • w)^[n] y := by
  induction n with
  | zero => simp only [pow_zero, hact.one, Function.iterate_zero, id_eq]
  | succ n ih =>
    rw [pow_succ', hact _ hg _ (pow_mem hg n), ih, Function.iterate_succ_apply']

lemma transl_fixed {b : k} (hb : b ≠ 0) {y : OnePoint k}
    (h : transl b • y = y) : y = ∞ := by
  cases y with
  | infty => rfl
  | coe z =>
    rw [transl_smul_coe, OnePoint.coe_eq_coe] at h
    exact (hb (add_left_cancel (h.trans (add_zero z).symm))).elim

variable [CharZero k]

/-- A translation by two and an element moving infinity imply non-elementarity. -/
theorem nonElem_of (hact : ActsOn Γ a) {K A : SL(2, ℝ)} (hK : K ∈ Γ) (hA : A ∈ Γ)
    (hKt : ∀ y : OnePoint k, a K • y = transl (2 : k) • y)
    (hAinf : a A • (∞ : OnePoint k) ≠ ∞) : NonElem Γ a := by
  intro Γ' _ hfi y
  by_contra hnone
  have hfixed (g : SL(2, ℝ)) (hg : g ∈ Γ') : a g • y = y := by
    by_contra hne
    exact hnone ⟨g, hg, hne⟩
  have htranslation : (fun w : OnePoint k ↦ a K • w) = (fun w ↦ transl (2 : k) • w) :=
    funext hKt
  have hpow (n : ℕ) (hn : 0 < n) (w : OnePoint k) (hw : a (K ^ n) • w = w) : w = ∞ := by
    rw [hact.smul_pow hK, htranslation, transl_iterate] at hw
    exact transl_fixed (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') two_ne_zero) hw
  obtain ⟨m, hm, -, hmMem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hfi hK
  have hy : y = ∞ := hpow m hm y (hfixed _ (Subgroup.mem_inf.mp hmMem).1)
  subst y
  have hAK : A * K * A⁻¹ ∈ Γ := mul_mem (mul_mem hA hK) (inv_mem hA)
  obtain ⟨n, hn, -, hnMem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hfi hAK
  have hconj := hfixed _ (Subgroup.mem_inf.mp hnMem).1
  rw [conj_pow, hact _ (mul_mem hA (pow_mem hK n)) _ (inv_mem hA),
    hact _ hA _ (pow_mem hK n)] at hconj
  let w : OnePoint k := a A⁻¹ • ∞
  have hw : a A • w = ∞ := by
    simpa only [w, inv_inv] using hact.inv (inv_mem hA) (∞ : OnePoint k)
  have hKw : a (K ^ n) • w = w :=
    (smul_left_cancel_iff (a A)).mp (hconj.trans hw.symm)
  rw [hpow n hn w hKw] at hw
  exact hAinf hw

end ProjectiveAction

open Fricke (nA nB coe_nA)

section NormalForm

variable {k : Type*} [NontriviallyNormedField k] [DecidableEq k]
  {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

lemma slMap_nA_infty (σ : ℝ →+* k) (hx : x ≠ 0) :
    slMap σ (nA hz hrel) • (∞ : OnePoint k) ≠ ∞ := by
  rw [Ne, smul_infty_eq_self_iff, coe_slMap, coe_nA]
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
  intro h
  exact hx (σ.injective (h.trans (map_zero σ).symm))

/-- The embedded Fricke normal form acts non-elementarily. -/
theorem nonElem_slMap [CharZero k] (σ : ℝ →+* k) (hx : x ≠ 0) :
    NonElem (Subgroup.closure {nA hz hrel, nB hz hrel}) (slMap σ) :=
  nonElem_of (actsOn_slMap σ _) (commK_mem hz hrel) (Subgroup.subset_closure (by simp))
    (slMap_commK hz hrel σ) (slMap_nA_infty hz hrel σ hx)

end NormalForm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
