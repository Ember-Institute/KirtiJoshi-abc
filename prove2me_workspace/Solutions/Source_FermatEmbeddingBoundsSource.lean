/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source: Heights/Local/Bounded.lean and Iut/Tripod/GeneralPosition.lean:170-205.
The explicit extension below transfers every embedding of the actual image field
through the inclusion into the same full point field used by LocalBounds.
-/
import Definitions.Def_FermatLocalBelyi
import Solutions.Source_TripodLocalEmbeddingBounds
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

set_option autoImplicit false

open NumberField
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Local

/-- The algebraically closed target extends every embedding. -/
theorem exists_ringHom_extension {F L E : Type*} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra.IsAlgebraic F L] [IsAlgClosed E] (σ : F →+* E) :
    ∃ τ : L →+* E, ∀ a : F, τ (algebraMap F L a) = σ a := by
  letI : Algebra F E := σ.toAlgebra
  let τ : L →ₐ[F] E := IsAlgClosed.lift
  exact ⟨τ.toRingHom, fun a => τ.commutes a⟩

/-- Restriction of the full all-embeddings bound to the actual image subfield.
Both evaluations and the same constant occur in the conclusion. -/
theorem allEmbedding_bounds_descend (F L : IntermediateField ℚ Tripod.Qbar)
    [FiniteDimensional ℚ L] (hFL : F ≤ L)
    {E : Type*} [NormedField E] [IsAlgClosed E]
    (a : F) (b : L) (hab : (a : Tripod.Qbar) = (b : Tripod.Qbar)) (c : ℝ)
    (hb : ∀ τ : L →+* E,
      |Real.log ‖τ b‖| ≤ c ∧ |Real.log ‖τ b - 1‖| ≤ c) :
    ∀ σ : F →+* E, |Real.log ‖σ a‖| ≤ c ∧ |Real.log ‖σ a - 1‖| ≤ c := by
  letI : Algebra F L := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have hab' : algebraMap F L a = b := Subtype.ext hab
  intro σ
  obtain ⟨τ, hτ⟩ := exists_ringHom_extension (L := L) σ
  have ha : τ b = σ a := by rw [← hab', hτ]
  simpa only [ha] using hb τ

end AbcAdaptation.Tripod.Local

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Source-faithful all-place bridge with the fixed `(d+1) * max c 0` scale. -/
theorem embeddingBoundsToSet_source (M : Model N) (hRF : ResiduesFinite M) :
    EmbeddingBoundsToSet M := by
  intro x φ d c hxd hx
  obtain ⟨hφ, h0, h1, hC, hp⟩ := hx
  letI : FiniteDimensional ℚ x.P.ResidueField := hRF x.P
  letI : FiniteDimensional ℚ x.fieldOf :=
    x.σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  let z : Tripod.Pt := belyiImage M φ x
  let a : Tripod.fieldOf z.1 := Tripod.gen z.1
  let b : x.fieldOf := evalInField M x φ hφ
  have hz : z = ⟨x.eval φ hφ, h0, h1⟩ := belyiImage_eq M φ x hφ h0 h1
  have hab : (a : Tripod.Qbar) = (b : Tripod.Qbar) := by
    change z.1 = x.eval φ hφ
    rw [hz]
  have hFL : Tripod.fieldOf z.1 ≤ x.fieldOf :=
    belyiImage_field_le M φ x ⟨hφ, h0, h1⟩
  have hdeg : Module.finrank ℚ (Tripod.fieldOf z.1) ≤ d :=
    (IntermediateField.finrank_le_of_le_right hFL).trans hxd
  have hC' := Local.allEmbedding_bounds_descend (Tripod.fieldOf z.1) x.fieldOf
    hFL a b hab c hC
  have hp' := Local.allEmbedding_bounds_descend (Tripod.fieldOf z.1) x.fieldOf
    hFL a b hab c hp
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  have hdle : (Module.finrank ℚ (Tripod.fieldOf z.1) : ℝ) * max c 0 ≤
      (d + 1) * max c 0 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg.trans (Nat.le_succ d)) hc0
  have hle1 : max c 0 ≤ (d + 1) * max c 0 := by
    have hd1 : (1 : ℝ) ≤ d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  change z ∈ (localCompactSet d c).set
  refine ⟨fun v hv => ?_, fun w => ?_⟩
  · have hchar : Tripod.residueChar v = 2 := Finset.mem_singleton.mp hv
    have hmem' : ((Tripod.residueChar v : ℕ) : 𝓞 (Tripod.fieldOf z.1)) ∈
        v.maximalIdeal.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact ringChar.Nat.cast_ringChar
    have hmem : ((2 : ℕ) : 𝓞 (Tripod.fieldOf z.1)) ∈ v.maximalIdeal.asIdeal := by
      simpa only [hchar] using hmem'
    have hv1 := Local.abs_log_finitePlace_le hc0 (y := a)
      (fun τ => ((hp' τ).1).trans (le_max_left _ _)) v hmem
    have hv2 := Local.abs_log_finitePlace_le hc0 (y := a - 1)
      (fun τ => by
        rw [map_sub, map_one]
        exact ((hp' τ).2).trans (le_max_left _ _)) v hmem
    exact ⟨hv1.trans hdle, hv2.trans hdle⟩
  · have hw1 := Local.abs_log_infinitePlace_le (y := a)
      (fun σ => ((hC' σ).1).trans (le_max_left _ (0 : ℝ))) w
    have hw2 := Local.abs_log_infinitePlace_le (y := a - 1)
      (fun σ => by
        rw [map_sub, map_one]
        exact ((hC' σ).2).trans (le_max_left _ (0 : ℝ))) w
    exact ⟨hw1.trans hle1, hw2.trans hle1⟩

end AbcAdaptation.Tripod.Fermat.Proper
