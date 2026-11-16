/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_Procession
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open scoped BigOperators

namespace AbcAdaptation.Reference.Iut
@[simp]
private lemma card_procLabels (j : ℕ) : (procLabels j).card = j + 1 := Nat.card_Iic j
namespace Procession
/-- The `i`-th capsule of the standard procession has `i + 2` labels: it is the label
set `S_{j+1}` with `j = i + 1`, of cardinality `j + 1`. -/
private lemma standard_capsule_card (n : ℕ) (i : Fin n) :
    ((standard n).capsule i).card = i + 2 := by
  simp [Capsule.card, standard]
end Procession
end AbcAdaptation.Reference.Iut

open AbcAdaptation.Reference.Iut

theorem AbcAdaptation.Reference.Iut.Theorem110Invariants.sum_card_standard {P : Procession ℕ} {L : ℕ} (hP : P = Procession.standard L)
    (f : ℕ → ℝ) :
    ∑ i : Fin P.length, f (P.capsule i).card = ∑ i : Fin L, f (i + 2) := by
  subst hP
  change (∑ i : Fin L, f ((Procession.standard L).capsule i).card) =
    ∑ i : Fin L, f (i + 2)
  exact Finset.sum_congr rfl fun i _ =>
    congrArg f (Procession.standard_capsule_card L i)
