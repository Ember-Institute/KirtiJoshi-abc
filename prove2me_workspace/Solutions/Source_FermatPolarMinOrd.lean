/-
Independent source-proof adaptation; validation is recorded in this unit's CI receipts.
Complete source proof bodies adapted from Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/LinearEquiv.lean.
Original license and author notices are retained below where present.
See SOURCE_LEDGER.json for exact hashes and transformations.
-/
import Solutions.Source_FermatPolarTupleHeight
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/

/-!
# Heights of tuples only depend on linear equivalence classes

For a tuple `s` write `A_s = −min_i div(s_i)` (so `A_s(P) = −minOrd P s`). The divisor of
the product tuple `s ⊗ t = (s_i t_j)` is `A_s + A_t`, and that of `r • s` is `A_s − div r`.
Combining this with the comparison theorem `tupleHeight_le_of_minOrd_le` and the Segre
identity, we get the basic invariance of heights attached to divisors: if
`A_s − A_{s'} = A_u − A_{u'} + div r` then `h_s − h_{s'} ≈ h_u − h_{u'}`
(`AbcAdaptation.Tripod.Fermat.Proper.PolarTuple.abs_tupleHeight_sub_sub_le`). This is [GenEll], Proposition 1.4 (i), (iii):
the BD-class of the height of a divisor depends only on its linear equivalence class, and is
additive.
-/

namespace AbcAdaptation.Tripod.Fermat.Proper.PolarTuple

open AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.PolarAbsolute
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K] {ι κ ι' κ' : Type*}
  [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

/-- The minimal order of a product tuple is the sum of the minimal orders. -/
theorem minOrd_mul {s : ι → K} {t : κ → K} (hs : ∃ i, s i ≠ 0) (ht : ∃ j, t j ≠ 0)
    (P : Place K) : minOrd P (fun p : ι × κ => s p.1 * t p.2) = minOrd P s + minOrd P t := by
  have hst : ∃ p : ι × κ, s p.1 * t p.2 ≠ 0 :=
    ⟨(normIdx P s hs, normIdx P t ht), mul_ne_zero (normIdx_ne_zero hs) (normIdx_ne_zero ht)⟩
  apply le_antisymm
  · have := minOrd_le (P := P) hst (j := (normIdx P s hs, normIdx P t ht))
      (mul_ne_zero (normIdx_ne_zero hs) (normIdx_ne_zero ht))
    rw [P.ord_mul (normIdx_ne_zero hs) (normIdx_ne_zero ht), ← minOrd_eq hs,
      ← minOrd_eq ht] at this
    exact this
  · rw [minOrd_eq hst]
    set p := normIdx P (fun p : ι × κ => s p.1 * t p.2) hst
    have hp : s p.1 * t p.2 ≠ 0 := normIdx_ne_zero hst
    rw [P.ord_mul (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)]
    exact add_le_add (minOrd_le hs (left_ne_zero_of_mul hp))
      (minOrd_le ht (right_ne_zero_of_mul hp))

/-- Scaling a tuple by `r ≠ 0` shifts its minimal order by `ord_P r`. -/
theorem minOrd_smul {s : ι → K} (hs : ∃ i, s i ≠ 0) {r : K} (hr : r ≠ 0) (P : Place K) :
    minOrd P (fun i => r * s i) = P.ord r + minOrd P s := by
  have hrs : ∃ i, r * s i ≠ 0 := ⟨normIdx P s hs, mul_ne_zero hr (normIdx_ne_zero hs)⟩
  apply le_antisymm
  · have := minOrd_le (P := P) hrs (j := normIdx P s hs) (mul_ne_zero hr (normIdx_ne_zero hs))
    rw [P.ord_mul hr (normIdx_ne_zero hs), ← minOrd_eq hs] at this
    exact this
  · rw [minOrd_eq hrs]
    set i := normIdx P (fun i => r * s i) hrs
    have hi : r * s i ≠ 0 := normIdx_ne_zero hrs
    rw [P.ord_mul hr (right_ne_zero_of_mul hi)]
    exact add_le_add_right (minOrd_le hs (right_ne_zero_of_mul hi)) _


end AbcAdaptation.Tripod.Fermat.Proper.PolarTuple
