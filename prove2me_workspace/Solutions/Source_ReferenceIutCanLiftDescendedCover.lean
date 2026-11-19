/-
Source: Pi1/Orbicurve/Descent.lean and Pi1/Orbicurve/Lefschetz.lean
at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.

The uniqueness condition is the coordinate-ring statement of SOmegaTY.
-/
import Solutions.Source_ReferenceIutCanLiftChangeParameter
import Solutions.Source_ReferenceIutCanLiftConstantExtensionEtale
import Solutions.Source_ReferenceIutCanLiftSignMultiplicity

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k Ω] [Algebra k K]
  [Algebra K Ω] [IsScalarTower k K Ω] [CharZero k] [CharZero K] {t s y : Ω}

/-- Every cover unramified over the quadratic field has a unique map to the sign quotient. -/
def QuadraticCoverRigidity (k : Type u) [Field k] [Algebra k Ω] [CharZero k] (t y : Ω) : Prop :=
  ∀ (F : IntermediateField (rationalBase k t) Ω) [FiniteDimensional (rationalBase k t) F]
    (hF : quadraticParameterField k t y ≤ F),
    (∀ w : Ideal (coordRing t F), w.IsMaximal → ramificationIndex hF w = 1) →
    ∀ g : coordRing t (⊥ : IntermediateField (rationalBase k t) Ω) →ₐ[k] coordRing t F,
      Function.Injective g → g.toRingHom.IsIntegral →
      (∀ w : Ideal (coordRing t F), w.IsMaximal →
        (letI := g.toRingHom.toAlgebra;
          w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase k t) Ω))) =
          signQuotientMultiplicity t y (w.comap g)) →
      g = ringMap (bot_le : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ F)

theorem lineEquiv_comap_constantExtension (ht : Transcendental k t)
    (hs : Transcendental k s) (htK : Transcendental K t) (hsK : Transcendental K s)
    (v' : Ideal (coordRing s (⊥ : IntermediateField (rationalBase K s) Ω))) :
    (v'.comap (changeParameterLineEquiv htK hsK).toRingEquiv.toRingHom).comap
      (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t))) =
    (v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := s)))).comap
      (changeParameterLineEquiv ht hs).toRingEquiv.toRingHom := by
  ext x
  obtain ⟨p, rfl⟩ := (constantExtensionLineEquiv ht).surjective x
  change changeParameterLineEquiv htK hsK
    (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t))
      (constantExtensionLineEquiv ht p)) ∈ v' ↔
    constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := s))
      (changeParameterLineEquiv ht hs (constantExtensionLineEquiv ht p)) ∈ v'
  rw [constantExtensionMap_constantExtensionLineEquiv ht htK p,
    changeParameterLineEquiv_apply htK hsK, changeParameterLineEquiv_apply ht hs,
    constantExtensionMap_constantExtensionLineEquiv hs hsK p]

variable [IsAlgClosed Ω]

theorem signQuotientMultiplicity_changeParameter_extension {b c : Ω}
    (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c)
    (ht : Transcendental k t) (hs : Transcendental k s)
    (htK : Transcendental K t) (hsK : Transcendental K s)
    (v' : Ideal (coordRing s (⊥ : IntermediateField (rationalBase K s) Ω))) (hv' : v'.IsMaximal)
    (hv₀ : v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K))) ≠ ⊥) :
    signQuotientMultiplicity t y (v'.comap (changeParameterLineEquiv htK hsK).toRingEquiv.toRingHom) =
      signQuotientMultiplicity t y
        ((v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K)))).comap
          (changeParameterLineEquiv ht hs).toRingEquiv.toRingHom) := by
  letI := hv'
  let e := (changeParameterLineEquiv ht hs).toRingEquiv
  let e' := (changeParameterLineEquiv htK hsK).toRingEquiv
  have he := lineEquiv_comap_constantExtension ht hs htK hsK v'
  have hmax : (v'.comap e'.toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e'.surjective
  have h₀ : (v'.comap e'.toRingHom).comap
      (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t))) ≠ ⊥ := by
    rw [he]
    intro hz
    apply hv₀
    have hbot : (⊥ : Ideal (coordRing s (⊥ : IntermediateField (rationalBase k s) Ω))).comap
        e.toRingHom = ⊥ :=
      Ideal.comap_bot_of_injective _ e.injective
    exact Ideal.comap_injective_of_surjective _ e.surjective (hz.trans hbot.symm)
  have h := signQuotientMultiplicity_constantExtension htK hb hc hy _ hmax h₀
  rw [he] at h
  exact h

variable [IsAlgClosed k]

private theorem parameterMap_ramification_descends {b c : Ω}
    (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c)
    {F : IntermediateField (rationalBase k t) Ω} {L : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F] [FiniteDimensional (rationalBase K t) L]
    (hFL : ∀ x ∈ F, x ∈ L) (hLF : L ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω))
    (ht : Transcendental k t) (hs : Transcendental k s)
    (htK : Transcendental K t) (hsK : Transcendental K s)
    (hsF : s ∈ F) (hsL : s ∈ L)
    (hst : IsIntegral (polynomialBase k t) s) (hts : IsIntegral (polynomialBase k s) t)
    (hstK : IsIntegral (polynomialBase K t) s) (htsK : IsIntegral (polynomialBase K s) t)
    (hK : ∀ w : Ideal (coordRing t L), w.IsMaximal →
      (letI := (parameterMap htK hsK hsL hstK htsK).toRingHom.toAlgebra;
        w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase K t) Ω))) =
        signQuotientMultiplicity t y (w.comap (parameterMap htK hsK hsL hstK htsK))) :
    ∀ w : Ideal (coordRing t F), w.IsMaximal →
      (letI := (parameterMap ht hs hsF hst hts).toRingHom.toAlgebra;
        w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase k t) Ω))) =
        signQuotientMultiplicity t y (w.comap (parameterMap ht hs hsF hst hts)) := by
  have hRebasedK := (parameterMap_ramification_iff htK hsK hsL hstK htsK
    (signQuotientMultiplicity t y)).mp hK
  letI : FiniteDimensional (rationalBase k s) (changeParameterField F hsF) :=
    finiteDimensional_changeParameter (hs := hsF) hts
  have hFLs : ∀ x ∈ changeParameterField F hsF, x ∈ changeParameterField L hsL := hFL
  have htF : t ∈ F := F.algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
  have htFs : t ∈ IntermediateField.adjoin (rationalBase K s) (changeParameterField F hsF : Set Ω) :=
    IntermediateField.subset_adjoin _ _ htF
  have hLFs : changeParameterField L hsL ≤
      IntermediateField.adjoin (rationalBase K s) (changeParameterField F hsF : Set Ω) :=
    fun x hx => adjoin_parameter_le htFs (hLF hx)
  let h₁ : (⊥ : IntermediateField (rationalBase k s) Ω) ≤ changeParameterField F hsF := bot_le
  let h₁' : (⊥ : IntermediateField (rationalBase K s) Ω) ≤ changeParameterField L hsL := bot_le
  have hRebased := etale_of_constantExtension hsK h₁ h₁' bot_mem_constantExtension hFLs bot_le hLFs
    (m₁ := fun v => signQuotientMultiplicity t y
      (v.comap (changeParameterLineEquiv ht hs).toRingEquiv.toRingHom))
    (m₁' := fun v' => signQuotientMultiplicity t y
      (v'.comap (changeParameterLineEquiv htK hsK).toRingEquiv.toRingHom))
    (m₂ := fun _ => 1) (m₂' := fun _ => 1)
    (signQuotientMultiplicity_changeParameter_extension hb hc hy ht hs htK hsK)
    (fun _ _ _ => rfl)
    (fun w hw => by simpa only [mul_one] using hRebasedK w hw)
  exact (parameterMap_ramification_iff ht hs hsF hst hts (signQuotientMultiplicity t y)).mpr
    (fun w hw => by simpa only [mul_one] using hRebased w hw)

/-- Descend both covers and use the lower sign quotient's rigidity to identify the upper map. -/
theorem quadraticCoverMap_eq_of_descended (htK : Transcendental K t) {b c : Ω}
    (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c)
    (hk : QuadraticCoverRigidity k t y)
    {F : IntermediateField (rationalBase k t) Ω} {L : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F] [FiniteDimensional (rationalBase K t) L]
    (hFL : ∀ x ∈ F, x ∈ L) (hLF : L ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω))
    (hyF : y ∈ F) (hL : quadraticParameterField K t y ≤ L)
    (hUnramified : ∀ w : Ideal (coordRing t L), w.IsMaximal → ramificationIndex hL w = 1)
    (g : coordRing t (⊥ : IntermediateField (rationalBase K t) Ω) →ₐ[K] coordRing t L)
    (hgIntegral : g.toRingHom.IsIntegral)
    (hgRamification : ∀ w : Ideal (coordRing t L), w.IsMaximal →
      (letI := g.toRingHom.toAlgebra;
        w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase K t) Ω))) =
        signQuotientMultiplicity t y (w.comap g))
    (hsF : coordRingVal t (g (constantExtensionLineEquiv htK X)) ∈ F) :
    g = ringMap (bot_le : (⊥ : IntermediateField (rationalBase K t) Ω) ≤ L) := by
  have ht : Transcendental k t := transcendental_of_constantExtension htK
  have hF : quadraticParameterField k t y ≤ F := IntermediateField.adjoin_simple_le_iff.mpr hyF
  have hUnramifiedF : ∀ w : Ideal (coordRing t F), w.IsMaximal → ramificationIndex hF w = 1 := by
    have h := etale_of_constantExtension htK hF hL quadraticParameterField_mem_extension hFL
      quadraticParameterField_le_extension_adjoin hLF
      (m₁ := fun _ => 1) (m₂ := fun _ => 1) (m₁' := fun _ => 1) (m₂' := fun _ => 1)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun w hw => by simpa only [mul_one] using hUnramified w hw)
    intro w hw
    simpa only [mul_one] using h w hw
  set s := coordRingVal t (g (constantExtensionLineEquiv htK X))
  have hsL : s ∈ L := (g (constantExtensionLineEquiv htK X) : L).2
  have hstK : IsIntegral (polynomialBase K t) s :=
    isIntegral_of_mem_coordRing t (g (constantExtensionLineEquiv htK X))
  have htsK : IsIntegral (polynomialBase K s) t := isIntegral_old_parameter htK g hgIntegral
  have hsK : Transcendental K s := transcendental_of_integral_parameter htK htsK
  have hs : Transcendental k s := transcendental_of_constantExtension hsK
  have hsint : IsIntegral (rationalBase k t) s :=
    (IsIntegral.of_finite (rationalBase k t) (⟨s, hsF⟩ : F)).map
      (IsScalarTower.toAlgHom (rationalBase k t) F Ω)
  have hst : IsIntegral (polynomialBase k t) s :=
    isIntegral_polynomialBase_of_constantExtension htK hsint hstK
  have htalg : IsAlgebraic (polynomialBase k s) t :=
    isAlgebraic_parameter_exchange hs hst.isAlgebraic
  have htint : IsIntegral (rationalBase k s) t :=
    ((IsFractionRing.isAlgebraic_iff (polynomialBase k s) (rationalBase k s) Ω).mp htalg).isIntegral
  have hts : IsIntegral (polynomialBase k s) t :=
    isIntegral_polynomialBase_of_constantExtension hsK htint htsK
  have hg : g = parameterMap htK hsK hsL hstK htsK := by
    apply parameterLineAlgHom_ext htK
    apply coordRingVal_injective t
    change s = _
    exact ((parameterMap_coordRingVal htK hsK hsL hstK htsK X).trans (aeval_X _)).symm
  rw [hg] at hgRamification
  have hRamificationF := parameterMap_ramification_descends hb hc hy hFL hLF ht hs htK hsK
    hsF hsL hst hts hstK htsK hgRamification
  have hgF := hk F hF hUnramifiedF (parameterMap ht hs hsF hst hts)
    (parameterMap_injective ht hs hsF hst hts)
    (parameterMap_isIntegral ht hs hsF hst hts) hRamificationF
  have hst_eq : s = t := by
    calc
      s = coordRingVal t (parameterMap ht hs hsF hst hts (constantExtensionLineEquiv ht X)) :=
        ((parameterMap_coordRingVal ht hs hsF hst hts X).trans (aeval_X _)).symm
      _ = coordRingVal t (ringMap (bot_le : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ F)
            (constantExtensionLineEquiv ht X)) :=
        congrArg (fun f => coordRingVal t (f (constantExtensionLineEquiv ht X))) hgF
      _ = t := (coe_constantExtensionLineEquiv ht X).trans (aeval_X t)
  apply parameterLineAlgHom_ext htK
  apply coordRingVal_injective t
  change s = _
  exact hst_eq.trans ((coe_constantExtensionLineEquiv htK X).trans (aeval_X t)).symm

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
