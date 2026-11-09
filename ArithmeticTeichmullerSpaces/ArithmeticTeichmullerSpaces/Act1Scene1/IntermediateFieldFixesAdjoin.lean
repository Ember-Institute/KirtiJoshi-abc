/-
Adapted from the already vendored GenuineNormalizationPrimeInertia.lean.
original-path: refer/iut/Iut/Anabelian/Genuine/Homs.lean
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-commit: b51b94cad5c729f753ed0790b5fb95d9d65aaff1
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modifications: isolate the fixed-field adjoin argument at the generic carrier
level, and transport its input membership over an equality of named bases.
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalization

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: fixed-field/adjoin closure of the existing
`Genuine.normalizationPrime_inertia_fixes_fullDivision` proof.
fidelity: isolates the algebraic generator-closure argument from actual seed
instances. Rebase transport preserves the original ambient elements.
boundary: no inertia, ramification, cusp or producer assertion occurs here.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open IntermediateField
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section

/-- Fixing the listed generators fixes every element of their ambient adjoin. -/
theorem fixes_adjoin_of_fixes_generators
    {B Ω : Type u} [Field B] [Field Ω] [Algebra B Ω]
    (N : IntermediateField B Ω) (τ : N ≃ₐ[B] N) (T : Set Ω)
    (hT : ∀ b ∈ T, ∃ hb : b ∈ N, τ ⟨b, hb⟩ = ⟨b, hb⟩)
    (a : N) (ha : (a : Ω) ∈ IntermediateField.adjoin B T) : τ a = a := by
  let F' : IntermediateField B Ω :=
    { carrier := {b | ∃ hb : b ∈ N, τ ⟨b, hb⟩ = ⟨b, hb⟩}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by
          have ht := congrArg₂ (· * ·) ha' hb'
          simpa [← map_mul] using ht⟩
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨add_mem ha hb, by
          have ht := congrArg₂ (· + ·) ha' hb'
          simpa [← map_add] using ht⟩
      algebraMap_mem' := fun c => ⟨N.algebraMap_mem c, τ.commutes c⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        change τ ((⟨a, ha⟩ : N)⁻¹) = (⟨a, ha⟩ : N)⁻¹
        rw [map_inv₀, ha'] }
  have hle : IntermediateField.adjoin B T ≤ F' :=
    IntermediateField.adjoin_le_iff.mpr hT
  obtain ⟨_, hfix⟩ := hle ha
  exact hfix

/-- An equality of named base fields preserves the ambient adjoin. -/
theorem rebaseField_eq_adjoin
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    {B B' : IntermediateField k Ω} (h : B = B') (T : Set Ω) :
    rebaseField h (IntermediateField.adjoin B T) = IntermediateField.adjoin B' T := by
  subst B'
  ext a
  rfl

/-- The generator-fixation argument can consume membership over the original base. -/
theorem fixes_rebased_adjoin
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    {B B' : IntermediateField k Ω} (h : B = B')
    (N : IntermediateField B' Ω) (τ : N ≃ₐ[B'] N) (T : Set Ω)
    (hT : ∀ b ∈ T, ∃ hb : b ∈ N, τ ⟨b, hb⟩ = ⟨b, hb⟩)
    (a : N) (ha : (a : Ω) ∈ IntermediateField.adjoin B T) : τ a = a := by
  have hm : (a : Ω) ∈ rebaseField h (IntermediateField.adjoin B T) :=
    (mem_rebaseField h _ _).mpr ha
  rw [rebaseField_eq_adjoin h T] at hm
  exact fixes_adjoin_of_fixes_generators N τ T hT a hm

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
