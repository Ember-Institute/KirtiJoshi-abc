/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: refer/iut/Iut/Cor312/Procession.lean
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
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Nat

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# Capsules and processions (taxis #43)

Combinatorial backbone of the **large volume container** of the Corollary 3.12 variant
(taxis #33): capsules of labels and processions of capsules, together with the standard
label sets `S_{j+1} = {0, 1, …, j}` of the procession of tensor-packets of log-shells.

## Source correspondence

* Capsules and processions of label sets: IUT I, §§4–6 (in particular the processions of
  ±-label capsules of IUT I, Proposition 6.9).
* The label sets `S_{j+1}` and the procession whose `j`-th capsule has label set
  `S_{j+1}` (`j = 1, …, ℓ*`): IUT III, Propositions 3.1–3.3; Hoshi, *Introduction to
  inter-universal Teichmüller theory (continued)*, §13.

This module records only the combinatorics: the tensor-packets themselves are built on
top of these labels in `Iut.Cor312.Container`. Nothing here asserts any statement of the
IUT papers; the definitions are plain finite combinatorics.

## Main definitions

* `Iut.procLabels j`: the label set `S_{j+1} = {0, …, j}` as a `Finset ℕ`.
* `Iut.Capsule`: a capsule of labels, i.e. a finite set of labels.
* `Iut.Procession`: an increasing chain of capsules together with its inclusion maps.
* `Iut.Procession.standard n`: the standard procession `S_2 ⊆ S_3 ⊆ ⋯ ⊆ S_{n+1}` of the
  tensor-packet construction, with `n = ℓ* = (ℓ - 1)/2` in the intended instantiation.
-/

namespace Iut

/-- The label set `S_{j+1} = {0, 1, …, j}` of IUT III, Propositions 3.1–3.3, a finite
set of `j + 1` labels. The index convention follows the papers: the *subscript* of `S`
is the cardinality, so `procLabels j` is the set called `S_{j+1}`. -/
def procLabels (j : ℕ) : Finset ℕ := Finset.Iic j

lemma procLabels_mono {i j : ℕ} (h : i ≤ j) : procLabels i ⊆ procLabels j :=
  Finset.Iic_subset_Iic.mpr h

/-- A **capsule** of labels drawn from `ι`: a finite collection of labels
(IUT I, §4). The objects indexed by a capsule (prime strips, log-shells, …) are
attached on top of this combinatorial datum by the container modules. -/
structure Capsule (ι : Type*) where
  /-- The finite set of labels of the capsule. -/
  labels : Finset ι

namespace Capsule

variable {ι : Type*}

/-- The number of labels of a capsule. -/
def card (S : Capsule ι) : ℕ := S.labels.card

/-- The label set of a capsule, as a type. -/
def LabelType (S : Capsule ι) : Type _ := S.labels

instance [DecidableEq ι] (S : Capsule ι) : DecidableEq S.LabelType :=
  inferInstanceAs (DecidableEq S.labels)

instance (S : Capsule ι) : Fintype S.LabelType :=
  inferInstanceAs (Fintype S.labels)

end Capsule

/-- A **procession** of capsules (IUT I, §§4–6): a finite increasing chain of capsules.
The inclusion maps of the chain are recorded by `labels_mono`; see
`Procession.inclusion` for the induced maps of label types. -/
structure Procession (ι : Type*) where
  /-- The number of capsules in the procession. -/
  length : ℕ
  /-- The capsules of the procession. -/
  capsule : Fin length → Capsule ι
  /-- Monotonicity: the labels of the capsules form an increasing chain. This datum
  encodes the inclusion maps of the procession. -/
  labels_mono : ∀ ⦃i j : Fin length⦄, i ≤ j → (capsule i).labels ⊆ (capsule j).labels

namespace Procession

variable {ι : Type*} (P : Procession ι)

/-- The **standard procession** of the tensor-packet construction: the chain
`S_2 ⊆ S_3 ⊆ ⋯ ⊆ S_{n+1}` of label sets, where the `i`-th capsule (`i = 0, …, n-1`,
corresponding to the paper's index `j = i + 1 ∈ {1, …, ℓ*}`) has label set
`S_{j+1} = {0, 1, …, j}`. In the intended instantiation `n = ℓ* = (ℓ - 1)/2` for the
prime `ℓ` of the initial Θ-data (IUT III, Propositions 3.1–3.3). -/
def standard (n : ℕ) : Procession ℕ where
  length := n
  capsule i := ⟨procLabels (i + 1)⟩
  labels_mono i j h := procLabels_mono (by exact Nat.add_le_add_right h 1)

end Procession

end Iut

end AbcAdaptation.Reference
