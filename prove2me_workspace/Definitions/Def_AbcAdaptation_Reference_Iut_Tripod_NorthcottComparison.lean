/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Sources: Tripod/Basic.lean:425,451,457. Exact NorthcottHyp definition and
northcott/northcott_of_equiv proof bodies; namespaces/imports adapted.
The closed northcottHyp theorem reuses the existing proved concrete Northcott
rather than replaying the same polynomial proof.
-/
import Definitions.Def_AbcAdaptation_Reference_Genl_DiscrepancyEquivGe
import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference

def NorthcottHyp : Prop :=
  ∀ (d : ℕ) (H : ℝ), {x : Pt | x ∈ ptLE d ∧ htCan x ≤ H}.Finite

/-- Existing full bounded-degree Northcott, definitionally the source proposition. -/
theorem northcottHyp : NorthcottHyp := boundedDegreeFiniteness

theorem northcott (hN : NorthcottHyp) (K : CompactlyBounded) (d : ℕ) (H : ℝ) :
    {x : Pt | x ∈ K.set ∩ ptLE d ∧ htCan x ≤ H}.Finite :=
  (hN d H).subset fun _ hx ↦ ⟨hx.1.2, hx.2⟩

/-- The Northcott finiteness for a function `h` with `(1/6) h ≈ htCan` on `K`, as in
`Iut.CurveInputs.northcott`: a bound on `h` implies a bound on `htCan`. -/
theorem northcott_of_equiv (hN : NorthcottHyp) (K : CompactlyBounded) (d : ℕ)
    {h : Pt → ℝ} (hh : ((1 / 6 : ℝ) • h) ≈[K.set] htCan) (H : ℝ) :
    {x : Pt | x ∈ K.set ∩ ptLE d ∧ h x ≤ H}.Finite := by
  obtain ⟨C, hC⟩ := hh.ge
  refine (northcott hN K d (H / 6 + C)).subset fun x hx ↦ ⟨hx.1, ?_⟩
  have := hC x hx.1.1
  simp only [Pi.smul_apply, smul_eq_mul] at this
  linarith [hx.2]

end AbcAdaptation.Tripod
