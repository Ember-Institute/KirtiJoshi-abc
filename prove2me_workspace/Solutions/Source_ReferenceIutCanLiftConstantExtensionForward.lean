/-
Source: Pi1/Orbicurve/BaseChange.lean and Pi1/Orbicurve/Lefschetz.lean
at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftConstantExtensionRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationSquare

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin Pointwise

universe u

noncomputable section

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω]
  [Algebra k Ω] [IsScalarTower k K Ω] {t : Ω}

attribute [local instance] fieldRingAction

private theorem constantExtensionInertia_le_bot
    {N : IntermediateField (rationalBase k t) Ω} {N' : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N]
    (hN : ∀ x ∈ N, x ∈ N')
    (hN' : N' ≤ IntermediateField.adjoin (rationalBase K t) (N : Set Ω))
    (u' : Ideal (coordRing t N')) (hu : u'.comap (constantExtensionMap hN) = ⊥) :
    u'.inertia (N' ≃ₐ[rationalBase K t] N') ≤ ⊥ := by
  intro σ' hσ'
  rw [Subgroup.mem_bot]
  have h := constantExtensionRes_mem_inertia hN u' σ' hσ'
  rw [hu] at h
  have hcoeff (a : coordRing t N) : constantExtensionRes hN σ' (a : N) = (a : N) := by
    have ha : constantExtensionRes hN σ' • a - a ∈ (⊥ : Ideal (coordRing t N)) := h a
    exact congrArg (fun b : coordRing t N => (b : N))
      (sub_eq_zero.mp (Ideal.mem_bot.mp ha))
  have hres : constantExtensionRes hN σ' = 1 := by
    letI := fractionFieldRing t N
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := coordRing t N) x
    change constantExtensionRes hN σ' ((a : N) / (b : N)) = (a : N) / (b : N)
    rw [map_div₀, hcoeff a, hcoeff b]
  exact constantExtensionRes_injective hN hN' (hres.trans (map_one _).symm)

variable [IsAlgClosed Ω] [CharZero k]

/-- The ramification index is one at a closed prime whose contraction is zero. -/
theorem ramificationIdx_constantExtension_of_comap_bot (htK : Transcendental K t)
    {F₂ : IntermediateField (rationalBase k t) Ω}
    {F₁' F₂' : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F₂] (h' : F₁' ≤ F₂')
    (h₂ : ∀ x ∈ F₂, x ∈ F₂')
    (h₂' : F₂' ≤ IntermediateField.adjoin (rationalBase K t) (F₂ : Set Ω))
    (w' : Ideal (coordRing t F₂')) [hw' : w'.IsMaximal]
    (hw₀ : w'.comap (constantExtensionMap h₂) = ⊥) :
    ramificationIndex h' w' = 1 := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨N, N', hF₂N, hNdim, hNgal, hN'dim, hN'gal, hNN', hN'⟩ :=
    exists_galois_constantExtension (K := K) F₂
  letI := hNdim
  letI := hNgal
  letI := hN'dim
  letI := hN'gal
  have hF₂'N' : F₂' ≤ N' := by
    rw [hN']
    exact h₂'.trans (IntermediateField.adjoin.mono _ _ _ hF₂N)
  obtain ⟨u', hu', hu'w⟩ := normalization_exists_maximal_over hF₂'N' w' hw'
  letI := hu'
  let u := u'.comap (constantExtensionMap hNN')
  have hcomap : u.comap (ringMap hF₂N) = w'.comap (constantExtensionMap h₂) := by
    rw [← hu'w]
    ext x
    exact Iff.rfl
  have hu₀ : u = ⊥ := by
    letI := ringMapAlgebra hF₂N
    letI : Algebra.IsIntegral (coordRing t F₂) (coordRing t N) := ⟨ringMap_isIntegral hF₂N⟩
    exact Ideal.eq_bot_of_comap_eq_bot (hcomap.trans hw₀)
  have hinertia := constantExtensionInertia_le_bot hNN' (le_of_eq hN') u' hu₀
  rw [← hu'w]
  apply (ramificationIdx_eq_one_iff htK h' hF₂'N' u').mpr
  exact inf_le_left.trans (hinertia.trans bot_le)

omit [IsAlgClosed Ω] in
private theorem isMaximal_comap_constantExtension_of_ne_bot (htK : Transcendental K t)
    {F : IntermediateField (rationalBase k t) Ω}
    {F' : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F] (hF : ∀ x ∈ F, x ∈ F')
    (w' : Ideal (coordRing t F')) [w'.IsPrime] (hw₀ : w'.comap (constantExtensionMap hF) ≠ ⊥) :
    (w'.comap (constantExtensionMap hF)).IsMaximal := by
  letI : CharZero (rationalBase k t) :=
    charZero_of_injective_algebraMap (algebraMap k (rationalBase k t)).injective
  letI : Algebra.IsSeparable (rationalBase k t) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI := dedekindRing t (transcendental_of_constantExtension htK) F
  exact Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _) hw₀

/-- Extending constants preserves the equality of cover multiplicities at closed primes. -/
theorem etale_constantExtension (htK : Transcendental K t)
    {F₁ F₂ : IntermediateField (rationalBase k t) Ω}
    {F₁' F₂' : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F₂] (h : F₁ ≤ F₂) (h' : F₁' ≤ F₂')
    (h₁ : ∀ x ∈ F₁, x ∈ F₁') (h₂ : ∀ x ∈ F₂, x ∈ F₂')
    (h₁' : F₁' ≤ IntermediateField.adjoin (rationalBase K t) (F₁ : Set Ω))
    (h₂' : F₂' ≤ IntermediateField.adjoin (rationalBase K t) (F₂ : Set Ω))
    {m₁ : Ideal (coordRing t F₁) → ℕ} {m₂ : Ideal (coordRing t F₂) → ℕ}
    {m₁' : Ideal (coordRing t F₁') → ℕ} {m₂' : Ideal (coordRing t F₂') → ℕ}
    (hm₁₀ : ∀ v' : Ideal (coordRing t F₁'), v'.IsMaximal →
      v'.comap (constantExtensionMap h₁) = ⊥ → m₁' v' = 1)
    (hm₁ : ∀ v' : Ideal (coordRing t F₁'), v'.IsMaximal →
      v'.comap (constantExtensionMap h₁) ≠ ⊥ → m₁' v' = m₁ (v'.comap (constantExtensionMap h₁)))
    (hm₂₀ : ∀ w' : Ideal (coordRing t F₂'), w'.IsMaximal →
      w'.comap (constantExtensionMap h₂) = ⊥ → m₂' w' = 1)
    (hm₂ : ∀ w' : Ideal (coordRing t F₂'), w'.IsMaximal →
      w'.comap (constantExtensionMap h₂) ≠ ⊥ → m₂' w' = m₂ (w'.comap (constantExtensionMap h₂)))
    (C : ∀ w : Ideal (coordRing t F₂), w.IsMaximal →
      ramificationIndex h w * m₂ w = m₁ (w.comap (ringMap h))) :
    ∀ w' : Ideal (coordRing t F₂'), w'.IsMaximal →
      ramificationIndex h' w' * m₂' w' = m₁' (w'.comap (ringMap h')) := by
  intro w' hw'
  letI := hw'
  letI : w'.IsPrime := hw'.isPrime
  let w := w'.comap (constantExtensionMap h₂)
  let v' := w'.comap (ringMap h')
  have hv : v'.comap (constantExtensionMap h₁) = w.comap (ringMap h) := by
    ext x
    exact Iff.rfl
  have hv' : v'.IsMaximal := normalization_comap_isMaximal h' w' hw'
  change ramificationIndex h' w' * m₂' w' = m₁' v'
  by_cases hw₀ : w = ⊥
  · have hv₀ : v'.comap (constantExtensionMap h₁) = ⊥ := by
      rw [hv, hw₀]
      exact Ideal.comap_bot_of_injective _ (ringMap_injective h)
    rw [ramificationIdx_constantExtension_of_comap_bot htK h' h₂ h₂' w' hw₀,
      hm₂₀ w' hw' hw₀, hm₁₀ v' hv' hv₀, one_mul]
  · have hwm := isMaximal_comap_constantExtension_of_ne_bot htK h₂ w' hw₀
    have hv₀ : v'.comap (constantExtensionMap h₁) ≠ ⊥ := by
      rw [hv]
      letI := ringMapAlgebra h
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw₀
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (ringMap_isIntegral h x)
    have he := ramificationIdx_constantExtension_eq htK h h' h₁ h₂ h₁' h₂' w' hw₀
    change ramificationIndex h' w' = ramificationIndex h w at he
    rw [he, hm₂ w' hw' hw₀, hm₁ v' hv' hv₀, hv]
    exact C w hwm

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
