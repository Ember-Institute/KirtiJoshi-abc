/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveDeriv/Basic.lean polynomial-adjoin construction.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: cf1b11adab96fbd7d7bb5114e7215dcbf8b8cda1a8eda573e9759ac5316f40b2.
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Polynomial IntermediateField
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] (t : K)

/-- The value in `K` of the isomorphism `ℚ[X] ≃ ℚ[t]` is evaluation at `t`. -/
theorem coe_algEquivOfTranscendental (ht : Transcendental ℚ t) (p : ℚ[X]) :
    ((Polynomial.algEquivOfTranscendental ℚ t ht p : Algebra.adjoin ℚ {t}) : K) = aeval t p := by
  rw [Polynomial.algEquivOfTranscendental_apply]
  exact (aeval_algHom_apply (Algebra.adjoin ℚ {t}).val _ p).symm

theorem aeval_algEquivOfTranscendental_symm (ht : Transcendental ℚ t)
    (a : Algebra.adjoin ℚ {t}) :
    aeval t ((Polynomial.algEquivOfTranscendental ℚ t ht).symm a) = (a : K) := by
  rw [← coe_algEquivOfTranscendental t ht, AlgEquiv.apply_symm_apply]

/-- The derivation `d/dt : ℚ[t] → K` on the polynomial ring `ℚ[t] ⊆ K`, for `t`
transcendental over `ℚ`. -/
noncomputable def polyDeriv (ht : Transcendental ℚ t) : Derivation ℚ (Algebra.adjoin ℚ {t}) K where
  toFun a := aeval t (derivative ((Polynomial.algEquivOfTranscendental ℚ t ht).symm a))
  map_add' a b := by simp
  map_smul' q a := by simp
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change aeval t (derivative ((Polynomial.algEquivOfTranscendental ℚ t ht).symm (a * b))) =
      (a : K) * aeval t (derivative ((Polynomial.algEquivOfTranscendental ℚ t ht).symm b)) +
      (b : K) * aeval t (derivative ((Polynomial.algEquivOfTranscendental ℚ t ht).symm a))
    simp only [map_mul, derivative_mul, map_add, aeval_algEquivOfTranscendental_symm]
    ring

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem formallyEtale_adjoin [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    Algebra.FormallyEtale (Algebra.adjoin ℚ {t}) K := by
  have : Algebra.FormallyEtale (Algebra.adjoin ℚ {t}) ℚ⟮t⟯ :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Algebra.adjoin ℚ {t}))
  have : Algebra.FormallyEtale ℚ⟮t⟯ K := Algebra.FormallyEtale.of_isSeparable _ _
  exact Algebra.FormallyEtale.comp _ ℚ⟮t⟯ K

end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv
