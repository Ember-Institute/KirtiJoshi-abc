/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/NoncriticalP1/ElemMap.lean, Analytic.lean, Reduction.lean.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: ElemMap=5a39ddb83c19b37af76e573f522463e7baa167cd4dbce8a90c9c3a8d173c63a5; Analytic=32ac8aca84e7cfe15e10dab7ca99781a664ed0c44e32ea80906d538e1cb2c4d1; Reduction=097aace5620aa31d0eb75b0f976cffff02d655ebcd3c15fd6cee9726f101bc53.
-/
import Definitions.Def_FermatNoncriticalFunctions
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1

/-- Source `ofRat`, on the existing concrete projective-line type. -/
noncomputable def ofRat (q : ℚ) : Pt := some (q : Tripod.Qbar)

/-- All automorphisms of the full algebraic closure are quantified. -/
def IsGalStable (T : Finset Tripod.Qbar) : Prop :=
  ∀ σ : Tripod.Qbar ≃ₐ[ℚ] Tripod.Qbar, ∀ t ∈ T, σ t ∈ T

/-- Source degree over ℚ, without replacing algebraic points by rational points. -/
noncomputable abbrev deg (x : Tripod.Qbar) : ℕ := (minpoly ℚ x).natDegree

/-- Source branch set, including the point at infinity. -/
def withInf (T : Finset Tripod.Qbar) : Set Pt := insert none (some '' (T : Set Tripod.Qbar))

@[simp] theorem none_mem_withInf (T : Finset Tripod.Qbar) : (none : Pt) ∈ withInf T :=
  Set.mem_insert _ _

theorem some_mem_withInf {T : Finset Tripod.Qbar} {t : Tripod.Qbar} (ht : t ∈ T) :
    some t ∈ withInf T :=
  Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩

/-- Source fixed complex embedding, not an assumed norm law. -/
noncomputable def ι : Tripod.Qbar →ₐ[ℚ] ℂ :=
  letI : Algebra.IsAlgebraic ℚ Tripod.Qbar := AlgebraicClosure.isAlgebraic ℚ
  IsAlgClosed.lift

@[simp] theorem ι_ratCast (q : ℚ) : ι (q : Tripod.Qbar) = (q : ℂ) := map_ratCast ι q

@[simp] theorem norm_ι_ratCast (q : ℚ) : ‖ι (q : Tripod.Qbar)‖ = |(q : ℝ)| := by
  rw [ι_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

/-- A transparent conjunction of the exact three source conditions. Every
function here is the existing evaluation or ramification function of a list
of actual rational elementary maps. -/
def IsNoncriticalBelyi (hs : List ElemMap) (S : Set Pt) (τ : Pt) : Prop :=
  (∀ z ∈ S, evalComp hs z ∈ zeroOneInf) ∧
  evalComp hs τ ∉ zeroOneInf ∧
  (∀ z, 1 < ramIdxComp hs z → evalComp hs z ∈ zeroOneInf)

namespace IsNoncriticalBelyi

theorem mono {hs : List ElemMap} {S S' : Set Pt} {τ : Pt}
    (hg : IsNoncriticalBelyi hs S τ) (hS : S' ⊆ S) : IsNoncriticalBelyi hs S' τ :=
  ⟨fun z hz => hg.1 z (hS hz), hg.2.1, hg.2.2⟩

end IsNoncriticalBelyi

end AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1
