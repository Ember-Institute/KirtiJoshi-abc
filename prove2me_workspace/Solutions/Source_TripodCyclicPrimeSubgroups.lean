/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicLocal.lean (subgroups of prime order)
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

variable {X : Type*} [AddCommGroup X] {p : ℕ}

/-- Two distinct subgroups of prime order intersect trivially. -/
lemma addSubgroup_inf_eq_bot_of_card_prime (hp : p.Prime) {A B : AddSubgroup X}
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (hA ▸ hp.ne_zero)
  haveI : Finite B := Nat.finite_of_card_ne_zero (hB ▸ hp.ne_zero)
  have hdvd : Nat.card (A ⊓ B : AddSubgroup X) ∣ p := hA ▸ AddSubgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact AddSubgroup.card_eq_one.mp h1
  · have h1 : A ⊓ B = A := AddSubgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hA])
    have h2 : A ⊓ B = B := AddSubgroup.eq_of_le_of_card_ge inf_le_right (by rw [hp', hB])
    exact (hne (h1.symm.trans h2)).elim

/-- Two subgroups of order `p` with trivial intersection generate a containing
subgroup of order `p²`. -/
lemma addSubgroup_sup_eq_of_inf_eq_bot {A B T : AddSubgroup X} [Finite T]
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hT : Nat.card T = p * p)
    (hAT : A ≤ T) (hBT : B ≤ T) (hinf : A ⊓ B = ⊥) : A ⊔ B = T := by
  refine AddSubgroup.eq_of_le_of_card_ge (sup_le hAT hBT) ?_
  haveI : Finite ↥(A ⊔ B) :=
    Finite.of_injective (AddSubgroup.inclusion (sup_le hAT hBT)) (AddSubgroup.inclusion_injective _)
  let f : A × B → ↥(A ⊔ B) := fun x => ⟨x.1 + x.2, AddSubgroup.add_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : X) + b = a' + b' := congrArg Subtype.val h
    have hmem : (a : X) - a' ∈ A ⊓ B := by
      refine ⟨A.sub_mem a.2 a'.2, ?_⟩
      have : (a : X) - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add, h', add_comm]
      rw [this]
      exact B.sub_mem b'.2 b.2
    rw [hinf, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    have hb : (b : X) = b' := by
      rw [hmem] at h'
      exact add_left_cancel h'
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)
  simpa only [Nat.card_prod, hA, hB, hT] using Nat.card_le_card_of_injective f hf

/-- Each nonzero element of a subgroup of prime order has that order. -/
lemma addOrderOf_eq_of_mem_of_card_prime (hp : p.Prime) {A : AddSubgroup X}
    (hA : Nat.card A = p) {a : X} (ha : a ∈ A) (ha0 : a ≠ 0) : addOrderOf a = p := by
  have hdvd := addOrderOf_dvd_natCard (⟨a, ha⟩ : A)
  rw [← AddSubgroup.addOrderOf_coe, hA] at hdvd
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h
  · exact (ha0 (AddMonoid.addOrderOf_eq_one_iff.mp h1)).elim
  · exact h

/-- Each nonzero element of a subgroup of prime order generates the subgroup. -/
lemma zmultiples_eq_of_mem_of_card_prime (hp : p.Prime) {A : AddSubgroup X}
    (hA : Nat.card A = p) {a : X} (ha : a ∈ A) (ha0 : a ≠ 0) :
    AddSubgroup.zmultiples a = A := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (hA ▸ hp.ne_zero)
  refine AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr ha) ?_
  rw [Nat.card_zmultiples, addOrderOf_eq_of_mem_of_card_prime hp hA ha ha0, hA]

end AbcAdaptation.Reference.Iut
