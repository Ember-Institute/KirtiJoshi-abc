/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: refer/iut/Iut/Cor312/ThetaData/Places.lean
Original authors: The iut contributors
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original license: Apache-2.0; the original copyright and license notice is retained below.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Quotient
import Mathlib.Algebra.Ring.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Defs

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# Places of number fields for the Θ-data modules (taxis #39–#42)

Small helper layer over Mathlib's `NumberField.FinitePlace` and
`NumberField.InfinitePlace`: the combined type `Iut.Place` of all places `V(k)`, the
residue characteristic of a finite place, and the "lies over" relation between places
of an extension, all used by the initial Θ-data modules (IUT I, Definition 3.1).
-/

namespace Iut

open NumberField

variable (k : Type*) [Field k] [NumberField k]

/-- The set of places `V(k)` of a number field: finite (nonarchimedean) places and
infinite (archimedean) places (IUT I, Definition 3.1(b): `V_mod = V(F_mod)`). -/
def Place : Type _ := FinitePlace k ⊕ InfinitePlace k

variable {k}

namespace Place

/-- The nonarchimedean place attached to a finite place. -/
def finite (w : FinitePlace k) : Place k := Sum.inl w

/-- The archimedean place attached to an infinite place. -/
def infinite (w : InfinitePlace k) : Place k := Sum.inr w

end Place

/-- The **lies over** relation between finite places of an extension `K/k`: the prime of
`𝓞_K` attached to `w` lies over the prime of `𝓞_k` attached to `v` (`Ideal.LiesOver`; the
normalized absolute value of `w` restricts to a *power* of that of `v`, so the relation
is stated on the primes). -/
def FinitePlace.LiesOver {K : Type*} [Field K] [NumberField K] [Algebra k K]
    (w : FinitePlace K) (v : FinitePlace k) : Prop :=
  w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal

namespace Place

end Place

/-- The residue characteristic of a finite place: the characteristic of its residue
field. For a place over the rational prime `p` this is `p`. -/
noncomputable def residueChar (w : FinitePlace k) : ℕ :=
  ringChar (𝓞 k ⧸ w.maximalIdeal.asIdeal)

end Iut

end AbcAdaptation.Reference
