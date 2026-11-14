/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Modified adaptation, 2026-11-14: exact concrete Northcott proof from
refer/iut/Iut/Tripod/Northcott.lean. Uses the existing independent tripod
carrier and Mathlib only. Source hashes and revision status: SOURCE_MANIFEST.json.
-/
import Definitions.Def_TripodNorthcottInputs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Northcott

open NumberField Polynomial

/-- The coefficients of the minimal polynomial over `ℤ` of an algebraic integer `y` of a number
field `K` of degree `[K : ℚ] ≤ d` all of whose conjugates `φ y`, `φ : K →+* ℂ`, are bounded by
`B` lie in `[-coeffBoundOf d B, coeffBoundOf d B]` (`Polynomial.coeff_bdd_of_roots_le`). -/
theorem coeff_minpoly_int_mem_Icc {K : Type*} [Field K] [NumberField K] {y : K}
    (hy : IsIntegral ℤ y) {d : ℕ} (hd : Module.finrank ℚ K ≤ d) {B : ℝ}
    (hB : ∀ φ : K →+* ℂ, ‖φ y‖ ≤ B) (i : ℕ) :
    (minpoly ℤ y).coeff i ∈ Set.Icc (-(coeffBoundOf d B : ℤ)) (coeffBoundOf d B) := by
  have hpQ : minpoly ℚ y = (minpoly ℤ y).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hy
  have hpdeg : (minpoly ℚ y).natDegree ≤ d := (minpoly.natDegree_le _).trans hd
  have h := coeff_bdd_of_roots_le (B := B) (algebraMap ℚ ℂ)
    (minpoly.monic (Algebra.IsIntegral.isIntegral y))
    (IsAlgClosed.splits _) hpdeg (fun z hz ↦ ?_) i
  · rw [hpQ, Polynomial.map_map, coeff_map] at h
    have hcast : ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)) ((minpoly ℤ y).coeff i) =
        (((minpoly ℤ y).coeff i : ℤ) : ℂ) := by
      simp
    rw [hcast, Complex.norm_intCast] at h
    rw [Set.mem_Icc, ← abs_le, coeffBoundOf]
    exact_mod_cast h.trans (Nat.le_ceil _)
  · classical
    rw [← Multiset.mem_toFinset] at hz
    obtain ⟨φ, rfl⟩ := (Embeddings.range_eval_eq_rootSet_minpoly K ℂ y).symm.subset hz
    exact hB φ

end AbcAdaptation.Tripod.Northcott
