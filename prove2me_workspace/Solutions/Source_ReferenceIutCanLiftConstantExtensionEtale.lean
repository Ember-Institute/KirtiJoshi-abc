/-
Source: Pi1/Orbicurve/BaseChange.lean and Pi1/Orbicurve/Lefschetz.lean
at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftConstantExtensionRamification

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin Pointwise

universe u

noncomputable section

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω]
  [Algebra k Ω] [IsScalarTower k K Ω] [IsAlgClosed Ω] [CharZero k] {t : Ω}

attribute [local instance] galoisNormalizationCoeffComm fieldRingAction

local notation "F₀" => (⊥ : IntermediateField (rationalBase k t) Ω)
local notation "F₀'" => (⊥ : IntermediateField (rationalBase K t) Ω)

private theorem exists_maximal_comap_line [IsAlgClosed k]
    (htk : Transcendental k t) (htK : Transcendental K t)
    (p : Ideal (coordRing t F₀)) [p.IsMaximal] :
    ∃ v' : Ideal (coordRing t F₀'), v'.IsMaximal ∧
      v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t))) = p := by
  classical
  let ek : k[X] ≃ₐ[k] coordRing t F₀ := constantExtensionLineEquiv htk
  let eK : K[X] ≃ₐ[K] coordRing t F₀' := constantExtensionLineEquiv htK
  let P : Ideal k[X] := p.comap ek.toRingEquiv.toRingHom
  have hPm : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ ek.surjective
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal P).principal
  have hPq : P = Ideal.span {q} := hq
  have hqu : ¬ IsUnit q := fun h => hPm.ne_top (by rw [hPq, Ideal.span_singleton_eq_top]; exact h)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root q (fun h => hqu (Polynomial.isUnit_iff_degree_eq_zero.mpr h))
  have hPc : P = RingHom.ker (Polynomial.evalRingHom c) := by
    refine hPm.eq_of_le (RingHom.ker_ne_top _) ?_
    rw [hPq, Ideal.span_le, Set.singleton_subset_iff]
    exact hc
  let χ : coordRing t F₀' →+* K :=
    (Polynomial.evalRingHom (algebraMap k K c)).comp eK.symm.toRingEquiv.toRingHom
  have hχ : Function.Surjective χ := fun a => ⟨eK (Polynomial.C a), by simp [χ]⟩
  refine ⟨RingHom.ker χ, RingHom.ker_isMaximal_of_surjective χ hχ, ?_⟩
  ext x
  obtain ⟨r, rfl⟩ := ek.surjective x
  change χ (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t))
    (constantExtensionLineEquiv htk r)) = 0 ↔ r ∈ P
  rw [constantExtensionMap_constantExtensionLineEquiv htk htK, hPc, RingHom.mem_ker]
  have h1 : χ (constantExtensionLineEquiv htK (r.map (algebraMap k K))) =
      algebraMap k K (r.eval c) := by
    change Polynomial.eval (algebraMap k K c) (eK.symm (eK (r.map (algebraMap k K)))) = _
    rw [AlgEquiv.symm_apply_apply, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [h1, map_eq_zero_iff _ (algebraMap k K).injective] <;> rfl

section Galois

variable {N : IntermediateField (rationalBase k t) Ω}
  {N' : IntermediateField (rationalBase K t) Ω} (hN : ∀ x ∈ N, x ∈ N')
  [hNdim : FiniteDimensional (rationalBase k t) N] [hNgal : IsGalois (rationalBase k t) N]
  [hN'dim : FiniteDimensional (rationalBase K t) N'] [hN'gal : IsGalois (rationalBase K t) N']

include hNdim hNgal in
private theorem exists_smul_eq_over_line (htk : Transcendental k t)
    (u₁ u : Ideal (coordRing t N)) [u₁.IsPrime] [u.IsPrime]
    (hu : u₁.comap (ringMap (bot_le : F₀ ≤ N)) = u.comap (ringMap (bot_le : F₀ ≤ N))) :
    ∃ σ : fixSub N F₀, σ • u₁ = u := by
  let h : F₀ ≤ N := bot_le
  let p : Ideal (coordRing t F₀) := u.comap (ringMap h)
  letI : Algebra (coordRing t F₀) (coordRing t N) := ringMapAlgebra h
  letI := normalizationGaloisGroup_fixSub h htk
  letI : p.IsPrime := Ideal.comap_isPrime _ _
  letI : u.LiesOver p := ⟨rfl⟩
  letI : u₁.LiesOver p := ⟨hu.symm⟩
  exact Ideal.exists_smul_eq_of_isGaloisGroup p u₁ u (fixSub N F₀)

private theorem constantExtensionComap_smul (σ' : N' ≃ₐ[rationalBase K t] N')
    (u' : Ideal (coordRing t N')) :
    (σ' • u').comap (constantExtensionMap hN) =
      (constantExtensionRes hN σ') • u'.comap (constantExtensionMap hN) := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ← constantExtensionMap_smul]
  exact Iff.rfl

include hNdim hNgal hN'dim hN'gal in
private theorem exists_maximal_comap_galois [IsAlgClosed k] (htK : Transcendental K t)
    (u : Ideal (coordRing t N)) [hu : u.IsMaximal] :
    ∃ u' : Ideal (coordRing t N'), u'.IsMaximal ∧ u'.comap (constantExtensionMap hN) = u := by
  have htk : Transcendental k t := transcendental_of_constantExtension htK
  let h₀ : F₀ ≤ N := bot_le
  let h₀' : F₀' ≤ N' := bot_le
  let p : Ideal (coordRing t F₀) := u.comap (ringMap h₀)
  letI : p.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ (ringMap_isIntegral h₀) u
  obtain ⟨v', hv', hv'p⟩ := exists_maximal_comap_line htk htK p
  obtain ⟨w', hw', hw'v⟩ := normalization_exists_maximal_over h₀' v' hv'
  let w : Ideal (coordRing t N) := w'.comap (constantExtensionMap hN)
  letI : w'.IsPrime := hw'.isPrime
  letI : w.IsPrime := Ideal.comap_isPrime _ _
  letI : u.IsPrime := hu.isPrime
  have hwp : w.comap (ringMap h₀) = p := by
    rw [← hv'p, ← hw'v]
    ext x
    exact Iff.rfl
  obtain ⟨σ, hσ⟩ := exists_smul_eq_over_line htk w u hwp
  obtain ⟨σ', hσ'⟩ := constantExtensionRes_surjective htK hN (σ : N ≃ₐ[rationalBase k t] N)
  refine ⟨σ' • w', ?_, ?_⟩
  · rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ (MulSemiringAction.toRingAut _ _ σ').symm.surjective
  · rw [constantExtensionComap_smul hN σ' w', hσ']
    exact hσ

end Galois

/-- Every closed prime in the normalization over an algebraically closed constant field
is the contraction of a closed prime after extending constants. -/
theorem exists_maximal_comap_constantExtension [IsAlgClosed k] (htK : Transcendental K t)
    {F : IntermediateField (rationalBase k t) Ω} {F' : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F] (hF : ∀ x ∈ F, x ∈ F')
    (hF' : F' ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω))
    (w : Ideal (coordRing t F)) [hw : w.IsMaximal] :
    ∃ w' : Ideal (coordRing t F'), w'.IsMaximal ∧ w'.comap (constantExtensionMap hF) = w := by
  obtain ⟨N, N', hFN, hNdim, hNgal, hN'dim, hN'gal, hNN', hN'⟩ :=
    exists_galois_constantExtension (K := K) F
  letI := hNdim
  letI := hNgal
  letI := hN'dim
  letI := hN'gal
  have hF'N' : F' ≤ N' := by
    rw [hN']
    exact hF'.trans (IntermediateField.adjoin.mono _ _ _ hFN)
  obtain ⟨u, hu, huw⟩ := normalization_exists_maximal_over hFN w hw
  letI : u.IsMaximal := hu
  obtain ⟨u', hu', hu'u⟩ := exists_maximal_comap_galois hNN' htK u
  letI : u'.IsMaximal := hu'
  refine ⟨u'.comap (ringMap hF'N'),
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ (ringMap_isIntegral hF'N') u', ?_⟩
  rw [← huw, ← hu'u]
  ext x
  exact Iff.rfl

/-- Descend equality of cover multiplicities at closed primes under extension of constants. -/
theorem etale_of_constantExtension [IsAlgClosed k] (htK : Transcendental K t)
    {F₁ F₂ : IntermediateField (rationalBase k t) Ω}
    {F₁' F₂' : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F₂] (h : F₁ ≤ F₂) (h' : F₁' ≤ F₂')
    (h₁ : ∀ x ∈ F₁, x ∈ F₁') (h₂ : ∀ x ∈ F₂, x ∈ F₂')
    (h₁' : F₁' ≤ IntermediateField.adjoin (rationalBase K t) (F₁ : Set Ω))
    (h₂' : F₂' ≤ IntermediateField.adjoin (rationalBase K t) (F₂ : Set Ω))
    {m₁ : Ideal (coordRing t F₁) → ℕ} {m₂ : Ideal (coordRing t F₂) → ℕ}
    {m₁' : Ideal (coordRing t F₁') → ℕ} {m₂' : Ideal (coordRing t F₂') → ℕ}
    (hm₁ : ∀ v' : Ideal (coordRing t F₁'), v'.IsMaximal →
      v'.comap (constantExtensionMap h₁) ≠ ⊥ → m₁' v' = m₁ (v'.comap (constantExtensionMap h₁)))
    (hm₂ : ∀ w' : Ideal (coordRing t F₂'), w'.IsMaximal →
      w'.comap (constantExtensionMap h₂) ≠ ⊥ → m₂' w' = m₂ (w'.comap (constantExtensionMap h₂)))
    (C : ∀ w' : Ideal (coordRing t F₂'), w'.IsMaximal →
      (letI := ringMapAlgebra h'; w'.ramificationIdx (coordRing t F₁')) * m₂' w' =
        m₁' (w'.comap (ringMap h'))) :
    ∀ w : Ideal (coordRing t F₂), w.IsMaximal →
      (letI := ringMapAlgebra h; w.ramificationIdx (coordRing t F₁)) * m₂ w =
        m₁ (w.comap (ringMap h)) := by
  intro w hw
  letI := hw
  obtain ⟨w', hw', hw'w⟩ := exists_maximal_comap_constantExtension htK h₂ h₂' w
  letI := hw'
  have htk : Transcendental k t := transcendental_of_constantExtension htK
  have hw0 : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (notFieldRing t htk F₂)
  have hw'0 : w'.comap (constantExtensionMap h₂) ≠ ⊥ := hw'w.symm ▸ hw0
  have he := ramificationIdx_constantExtension_eq htK h h' h₁ h₂ h₁' h₂' w' hw'0
  have hv : (w'.comap (ringMap h')).comap (constantExtensionMap h₁) = w.comap (ringMap h) := by
    rw [← hw'w]
    ext x
    exact Iff.rfl
  have hv' : (w'.comap (ringMap h')).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ (ringMap_isIntegral h') w'
  have hv0 : w.comap (ringMap h) ≠ ⊥ := by
    letI := ringMapAlgebra h
    letI : Algebra.IsIntegral (coordRing t F₁) (coordRing t F₂) := ⟨ringMap_isIntegral h⟩
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw0
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  have hmem := C w' hw'
  rw [he, hm₂ w' hw' hw'0, hm₁ _ hv' (hv.symm ▸ hv0), hv, hw'w] at hmem
  exact hmem

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
