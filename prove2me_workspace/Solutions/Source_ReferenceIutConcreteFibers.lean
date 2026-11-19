/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Container.lean and Iut/Concrete/ThetaRegion.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalTheory

universe u v

open NumberField
open scoped BigOperators

variable {K : Type u} [Field K] [NumberField K] (LT : LocalTheory.{u, v} K)

/-- The rational place under a place of `K`. -/
noncomputable def toRational : Place K → RationalPlace
  | Sum.inl w => .finite ⟨residueChar w, LT.residueChar_prime w⟩
  | Sum.inr _ => .infinite

@[simp] lemma toRational_finite (w : FinitePlace K) :
    LT.toRational (Place.finite w) = .finite ⟨residueChar w, LT.residueChar_prime w⟩ := rfl

@[simp] lemma toRational_infinite (w : InfinitePlace K) :
    LT.toRational (Place.infinite w) = .infinite := rfl

/-- The places of `K` over a rational place. -/
abbrev Fiber (vQ : RationalPlace) : Type u := {v : Place K // LT.toRational v = vQ}

/-- The fiber over a prime `p`, identified with the finite places of residue
characteristic `p`. -/
def fiberFiniteEquiv (p : Nat.Primes) :
    LT.Fiber (.finite p) ≃ {w : FinitePlace K // residueChar w = p} where
  toFun v := match v with
    | ⟨Sum.inl w, h⟩ => ⟨w, by
        have h' := RationalPlace.finite.inj h
        exact congrArg Subtype.val h'⟩
    | ⟨Sum.inr _, h⟩ => absurd h (by simp [toRational])
  invFun w := ⟨Sum.inl w.1, by
    simp only [toRational]
    congr 1
    exact Subtype.ext w.2⟩
  left_inv v := by
    rcases v with ⟨v, h⟩
    rcases v with w | w
    · rfl
    · exact absurd h (by simp [toRational])
  right_inv w := rfl

/-- The fiber over the archimedean place, identified with the infinite places. -/
def fiberInfiniteEquiv : LT.Fiber .infinite ≃ InfinitePlace K where
  toFun v := match v with
    | ⟨Sum.inl _, h⟩ => absurd h (by simp [toRational])
    | ⟨Sum.inr w, _⟩ => w
  invFun w := ⟨Sum.inr w, rfl⟩
  left_inv v := by
    rcases v with ⟨v, h⟩
    rcases v with w | w
    · exact absurd h (by simp [toRational])
    · rfl
  right_inv w := rfl

/-- Finiteness of the fibers. -/
noncomputable instance fiberFintype (vQ : RationalPlace) : Fintype (LT.Fiber vQ) := by
  rcases vQ with p | _
  · haveI := LT.fiber_finite p
    haveI : Fintype {w : FinitePlace K // residueChar w = p} := Fintype.ofFinite _
    exact Fintype.ofEquiv _ (LT.fiberFiniteEquiv p).symm
  · exact Fintype.ofEquiv _ LT.fiberInfiniteEquiv.symm

/-- The family of places underlying a tuple of the fiber. -/
def tuple {ι : Type} (vQ : RationalPlace) (c : ι → LT.Fiber vQ) : ι → Place K :=
  fun j => (c j).1

/-- Every place of a tuple of the fiber over `p` lies over `p`. -/
lemma tuple_isOver {ι : Type} (p : Nat.Primes) (c : ι → LT.Fiber (.finite p)) :
    ∀ j, ∃ w : FinitePlace K, LT.tuple _ c j = Place.finite w ∧ residueChar w = p := by
  intro j
  have hv := (c j).2
  change LT.toRational (LT.tuple _ c j) = _ at hv
  rcases hw : LT.tuple _ c j with w | w
  · rw [hw] at hv
    exact ⟨w, rfl, congrArg Subtype.val (RationalPlace.finite.inj hv)⟩
  · rw [hw] at hv
    exact absurd hv (by simp [toRational])

/-- The weight of a place of `K` over a rational place. -/
noncomputable def weight (vQ : RationalPlace) (v : LT.Fiber vQ) : ℝ :=
  match v.1 with
  | Sum.inl w => placeWeight K w
  | Sum.inr w => infPlaceWeight K w

lemma finrank_pos : (0 : ℝ) < Module.finrank ℚ K := by
  exact_mod_cast Module.finrank_pos

lemma weight_pos (vQ : RationalPlace) (v : LT.Fiber vQ) : 0 < LT.weight vQ v := by
  rcases v with ⟨v, hv⟩
  rcases v with w | w
  · change 0 < placeWeight K w
    exact div_pos (by exact_mod_cast LT.localDeg_pos w) finrank_pos
  · change 0 < infPlaceWeight K w
    exact div_pos (by exact_mod_cast w.mult_pos) finrank_pos

lemma weight_sum_one (vQ : RationalPlace) : ∑ v, LT.weight vQ v = 1 := by
  rcases vQ with p | _
  · haveI := LT.fiber_finite p
    haveI : Fintype {w : FinitePlace K // residueChar w = p} := Fintype.ofFinite _
    have hsum := LT.sum_localDeg p p.2
    rw [Fintype.sum_equiv (LT.fiberFiniteEquiv p) (fun v => LT.weight (.finite p) v)
      (fun w => placeWeight K w.1)
      (fun v => by
        rcases v with ⟨v, hv⟩
        rcases v with w | w
        · rfl
        · exact absurd hv (by simp [toRational]))]
    simp only [placeWeight, ← Finset.sum_div]
    rw [div_eq_one_iff_eq finrank_pos.ne']
    rw [← Nat.cast_sum, hsum]
  · rw [Fintype.sum_equiv LT.fiberInfiniteEquiv (fun v => LT.weight .infinite v)
      (fun w => infPlaceWeight K w)
      (fun v => by
        rcases v with ⟨v, hv⟩
        rcases v with w | w
        · exact absurd hv (by simp [toRational])
        · rfl)]
    simp only [infPlaceWeight, ← Finset.sum_div]
    rw [div_eq_one_iff_eq finrank_pos.ne']
    exact_mod_cast LT.sum_mult

/-- The finite place underlying an element of the fiber over a prime. -/
noncomputable def fiberPlace {p : Nat.Primes} (v : LT.Fiber (.finite p)) : FinitePlace K :=
  (LT.fiberFiniteEquiv p v).1

lemma fiberPlace_spec {p : Nat.Primes} (v : LT.Fiber (.finite p)) :
    v.1 = Place.finite (LT.fiberPlace v) := by
  rcases v with ⟨v, hv⟩
  rcases v with w | w
  · rfl
  · exact absurd hv (by simp [toRational])

lemma residueChar_fiberPlace {p : Nat.Primes} (v : LT.Fiber (.finite p)) :
    residueChar (LT.fiberPlace v) = p :=
  (LT.fiberFiniteEquiv p v).2

end AbcAdaptation.Reference.Iut.LocalTheory
