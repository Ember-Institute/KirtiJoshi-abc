/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Modified adaptation, 2026-11-14: exact concrete Northcott proof from
refer/iut/Iut/Tripod/Northcott.lean. Uses the existing independent tripod
carrier and Mathlib only. Source hashes and revision status: SOURCE_MANIFEST.json.
-/
import Definitions.Def_TripodStatementIIInputs

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Northcott

open NumberField Polynomial

/-- The bound `exp (d · max H 0)` on the multiplicative height `exp (logHeight₁ (gen λ))` of a
point `λ` of degree `≤ d` and height `htCan λ ≤ H`. -/
noncomputable def heightBound (d : ℕ) (H : ℝ) : ℝ := Real.exp (d * max H 0)

theorem heightBound_pos (d : ℕ) (H : ℝ) : 0 < heightBound d H := Real.exp_pos _

/-- The degree of the minimal polynomial over `ℤ` of an algebraic integer `y` of a number field
`K` is at most `[K : ℚ]`. -/
theorem natDegree_minpoly_int_le {K : Type*} [Field K] [NumberField K] {y : K}
    (hy : IsIntegral ℤ y) : (minpoly ℤ y).natDegree ≤ Module.finrank ℚ K := by
  rw [← (minpoly.monic hy).natDegree_map (algebraMap ℤ ℚ),
    ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hy]
  exact minpoly.natDegree_le _

/-- The bound `⌈max B 1 ^ d · C(d, ⌊d/2⌋)⌉` on the coefficients of the minimal polynomial of an
algebraic integer of degree `≤ d` all of whose conjugates are bounded by `B`. -/
noncomputable def coeffBoundOf (d : ℕ) (B : ℝ) : ℕ := ⌈max B 1 ^ d * d.choose (d / 2)⌉₊

/-- The image of an algebraic integer `y` of a number field `K` in a field `L ⊇ K` is a root of
the minimal polynomial `minpoly ℤ y ∈ ℤ[X]` (stated with `eval₂` along `Int.castRingHom L`, to be
independent of the choice of the `ℤ`-algebra structure on `L`). -/
theorem eval₂_minpoly_int_algebraMap {K : Type*} [Field K] [NumberField K] (y : K)
    (L : Type*) [Field L] [Algebra K L] :
    (minpoly ℤ y).eval₂ (Int.castRingHom L) (algebraMap K L y) = 0 := by
  rw [← algebraMap_int_eq, ← aeval_def, aeval_algebraMap_apply, minpoly.aeval ℤ, map_zero]

/-- The bound on the coefficients of the minimal polynomial of `nλ` for a point `λ` of degree
`≤ d` and height `≤ H`, where `n ≤ heightBound d H` is a denominator of `λ`: the conjugates of
`nλ` are bounded by `heightBound d H ^ 2`. -/
noncomputable def coeffBound (d : ℕ) (H : ℝ) : ℕ :=
  coeffBoundOf d (heightBound d H * heightBound d H)

/-- The integer polynomials of degree `≤ d` with coefficients bounded by `coeffBound d H`. -/
def polySet (d : ℕ) (H : ℝ) : Set ℤ[X] :=
  {f | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ Set.Icc (-(coeffBound d H : ℤ)) (coeffBound d H)}

open scoped Classical in
/-- Exact finite root-set child, uniformly in both degree and height. -/
def FiniteRoots : Prop :=
  ∀ (d : ℕ) (H : ℝ),
    (⋃ f ∈ polySet d H, ((f.map (Int.castRingHom Qbar)).roots.toFinset : Set Qbar)).Finite

/-- Exact source witness for the same actual point x. All degrees, heights,
point fields and polynomial evaluations are fixed by existing definitions. -/
def PolynomialWitness : Prop :=
  ∀ {d : ℕ} {H : ℝ} {x : Pt}, x ∈ ptLE d → htCan x ≤ H →
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℝ) ≤ heightBound d H ∧ ∃ p ∈ polySet d H, p.Monic ∧
      p.eval₂ (Int.castRingHom Qbar) ((n : Qbar) * x.1) = 0

end AbcAdaptation.Tripod.Northcott
