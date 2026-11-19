/-
Source: Pi1/Orbicurve/HemiTY.lean and Pi1/Orbicurve/Lefschetz.lean
at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftConstantExtensionForward
import Solutions.Source_ReferenceIutCanLiftDescendedCover

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k Ω] [Algebra k K]
  [Algebra K Ω] [IsScalarTower k K Ω] [CharZero k] [CharZero K] [IsAlgClosed Ω] {t s y : Ω}

omit [CharZero K] in
private theorem finiteDimensional_constantExtension (F : IntermediateField (rationalBase k t) Ω)
    [FiniteDimensional (rationalBase k t) F] :
    FiniteDimensional (rationalBase K t) (IntermediateField.adjoin (rationalBase K t) (F : Set Ω)) := by
  obtain ⟨N, N', hFN, -, -, hN'dim, -, -, hN'⟩ :=
    exists_galois_constantExtension (K := K) F
  letI := hN'dim
  have hle : IntermediateField.adjoin (rationalBase K t) (F : Set Ω) ≤ N' := by
    rw [hN']
    exact IntermediateField.adjoin.mono _ _ _ hFN
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

private theorem signQuotientMultiplicity_constantExtension_of_comap_bot (htK : Transcendental K t)
    {b c : Ω} (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c)
    (v' : Ideal (coordRing t (⊥ : IntermediateField (rationalBase K t) Ω))) (hv' : v'.IsMaximal)
    (hv₀ : v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K))) = ⊥) :
    signQuotientMultiplicity t y v' = 1 := by
  let N := quadraticParameterField k t y
  let N' := quadraticParameterField K t y
  let h : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ N := bot_le
  let h' : (⊥ : IntermediateField (rationalBase K t) Ω) ≤ N' := bot_le
  let hN : ∀ x ∈ N, x ∈ N' := quadraticParameterField_mem_extension
  have hbK : b ∈ rationalBase K t := mem_rationalBase_extension hb
  have hcK : c ∈ rationalBase K t := mem_rationalBase_extension hc
  letI : FiniteDimensional (rationalBase k t) N := finiteDimensional_quadraticParameterField hb hc hy
  letI : FiniteDimensional (rationalBase K t) N' := finiteDimensional_quadraticParameterField hbK hcK hy
  letI : IsGalois (rationalBase K t) N' := isGalois_quadraticParameterField hbK hcK hy
  obtain ⟨w', hw', hw'v⟩ := normalization_exists_maximal_over h' v' hv'
  letI := hw'
  let w := w'.comap (constantExtensionMap hN)
  have hcomap : w.comap (ringMap h) =
      v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K))) := by
    rw [← hw'v]
    ext x
    exact Iff.rfl
  have hw₀ : w = ⊥ := by
    letI := ringMapAlgebra h
    letI : Algebra.IsIntegral (coordRing t (⊥ : IntermediateField (rationalBase k t) Ω))
        (coordRing t N) := ⟨ringMap_isIntegral h⟩
    exact Ideal.eq_bot_of_comap_eq_bot (hcomap.trans hv₀)
  have he := ramificationIdx_constantExtension_of_comap_bot htK h' hN
    quadraticParameterField_le_extension_adjoin w' hw₀
  rw [← hw'v]
  exact (signQuotientMultiplicity_eq_index htK w' hw').symm.trans he

private theorem signQuotientMultiplicity_changeParameter_of_comap_bot {b c : Ω}
    (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c)
    (ht : Transcendental k t) (hs : Transcendental k s)
    (htK : Transcendental K t) (hsK : Transcendental K s)
    (v' : Ideal (coordRing s (⊥ : IntermediateField (rationalBase K s) Ω))) (hv' : v'.IsMaximal)
    (hv₀ : v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K))) = ⊥) :
    signQuotientMultiplicity t y (v'.comap (changeParameterLineEquiv htK hsK).toRingEquiv.toRingHom) = 1 := by
  let e' := (changeParameterLineEquiv htK hsK).toRingEquiv
  have hmax : (v'.comap e'.toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e'.surjective
  refine signQuotientMultiplicity_constantExtension_of_comap_bot htK hb hc hy _ hmax ?_
  rw [lineEquiv_comap_constantExtension ht hs htK hsK v', hv₀]
  exact Ideal.comap_bot_of_injective _ (changeParameterLineEquiv ht hs).injective

private theorem quadraticCover_unramified_constantExtension (htK : Transcendental K t)
    {F : IntermediateField (rationalBase k t) Ω} {L : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F]
    (hF : quadraticParameterField k t y ≤ F) (hL : quadraticParameterField K t y ≤ L)
    (hFL : ∀ x ∈ F, x ∈ L) (hLF : L ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω))
    (hUnramified : ∀ w : Ideal (coordRing t F), w.IsMaximal → ramificationIndex hF w = 1) :
    ∀ w : Ideal (coordRing t L), w.IsMaximal → ramificationIndex hL w = 1 := by
  have he := etale_constantExtension htK hF hL quadraticParameterField_mem_extension hFL
    quadraticParameterField_le_extension_adjoin hLF
    (m₁ := fun _ => 1) (m₂ := fun _ => 1) (m₁' := fun _ => 1) (m₂' := fun _ => 1)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun w hw => by simpa only [mul_one] using hUnramified w hw)
  intro w hw
  simpa only [mul_one] using he w hw

private theorem parameterMap_ramification_constantExtension {b c : Ω}
    (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c)
    {F : IntermediateField (rationalBase k t) Ω} {L : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F] [FiniteDimensional (rationalBase K t) L]
    (hFL : ∀ x ∈ F, x ∈ L) (hLF : L ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω))
    (ht : Transcendental k t) (hs : Transcendental k s)
    (htK : Transcendental K t) (hsK : Transcendental K s)
    (hsF : s ∈ F) (hsL : s ∈ L)
    (hst : IsIntegral (polynomialBase k t) s) (hts : IsIntegral (polynomialBase k s) t)
    (hstK : IsIntegral (polynomialBase K t) s) (htsK : IsIntegral (polynomialBase K s) t)
    (hk : ∀ w : Ideal (coordRing t F), w.IsMaximal →
      (letI := (parameterMap ht hs hsF hst hts).toRingHom.toAlgebra;
        w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase k t) Ω))) =
        signQuotientMultiplicity t y (w.comap (parameterMap ht hs hsF hst hts))) :
    ∀ w : Ideal (coordRing t L), w.IsMaximal →
      (letI := (parameterMap htK hsK hsL hstK htsK).toRingHom.toAlgebra;
        w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase K t) Ω))) =
        signQuotientMultiplicity t y (w.comap (parameterMap htK hsK hsL hstK htsK)) := by
  have hRebased := (parameterMap_ramification_iff ht hs hsF hst hts
    (signQuotientMultiplicity t y)).mp hk
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
  have h := etale_constantExtension hsK h₁ h₁' bot_mem_constantExtension hFLs bot_le hLFs
    (m₁ := fun v => signQuotientMultiplicity t y
      (v.comap (changeParameterLineEquiv ht hs).toRingEquiv.toRingHom))
    (m₁' := fun v' => signQuotientMultiplicity t y
      (v'.comap (changeParameterLineEquiv htK hsK).toRingEquiv.toRingHom))
    (m₂ := fun _ => 1) (m₂' := fun _ => 1)
    (signQuotientMultiplicity_changeParameter_of_comap_bot hb hc hy ht hs htK hsK)
    (signQuotientMultiplicity_changeParameter_extension hb hc hy ht hs htK hsK)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun w hw => by simpa only [mul_one] using hRebased w hw)
  exact (parameterMap_ramification_iff htK hsK hsL hstK htsK (signQuotientMultiplicity t y)).mpr
    (fun w hw => by simpa only [mul_one] using h w hw)

/-- Rigidity of the sign quotient descends along an extension of the constant field. -/
theorem quadraticCoverRigidity_of_constantExtension (htK : Transcendental K t) {b c : Ω}
    (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c)
    (hK : QuadraticCoverRigidity K t y) :
    QuadraticCoverRigidity k t y := by
  intro F hFdim hF hUnramified g _ hgIntegral hgRamification
  letI : FiniteDimensional (rationalBase k t) F := hFdim
  let L := IntermediateField.adjoin (rationalBase K t) (F : Set Ω)
  letI : FiniteDimensional (rationalBase K t) L := finiteDimensional_constantExtension F
  have hFL : ∀ x ∈ F, x ∈ L := fun _ hx => IntermediateField.subset_adjoin _ _ hx
  have hyF : y ∈ F := hF (IntermediateField.mem_adjoin_simple_self (rationalBase k t) y)
  have hL : quadraticParameterField K t y ≤ L := IntermediateField.adjoin_simple_le_iff.mpr (hFL _ hyF)
  have hUnramifiedL := quadraticCover_unramified_constantExtension htK hF hL hFL le_rfl hUnramified
  have ht : Transcendental k t := transcendental_of_constantExtension htK
  let s := coordRingVal t (g (constantExtensionLineEquiv ht X))
  have hsF : s ∈ F := (g (constantExtensionLineEquiv ht X) : F).2
  have hsL : s ∈ L := hFL _ hsF
  have hst : IsIntegral (polynomialBase k t) s :=
    isIntegral_of_mem_coordRing t (g (constantExtensionLineEquiv ht X))
  have hts : IsIntegral (polynomialBase k s) t := isIntegral_old_parameter ht g hgIntegral
  have hs : Transcendental k s := transcendental_of_integral_parameter ht hts
  have hstK : IsIntegral (polynomialBase K t) s := isIntegral_polynomialBase_extension hst
  have htsK : IsIntegral (polynomialBase K s) t := isIntegral_polynomialBase_extension hts
  have hsK : Transcendental K s := transcendental_of_integral_parameter htK htsK
  have hg : g = parameterMap ht hs hsF hst hts := by
    apply parameterLineAlgHom_ext ht
    apply coordRingVal_injective t
    change s = _
    exact ((parameterMap_coordRingVal ht hs hsF hst hts X).trans (aeval_X _)).symm
  rw [hg] at hgRamification
  have hRamificationL := parameterMap_ramification_constantExtension hb hc hy hFL le_rfl ht hs
    htK hsK hsF hsL hst hts hstK htsK hgRamification
  have hgL := hK L hL hUnramifiedL (parameterMap htK hsK hsL hstK htsK)
    (parameterMap_injective htK hsK hsL hstK htsK)
    (parameterMap_isIntegral htK hsK hsL hstK htsK) hRamificationL
  have hst_eq : s = t := by
    calc
      s = coordRingVal t (parameterMap htK hsK hsL hstK htsK (constantExtensionLineEquiv htK X)) :=
        ((parameterMap_coordRingVal htK hsK hsL hstK htsK X).trans (aeval_X _)).symm
      _ = coordRingVal t (ringMap (bot_le : (⊥ : IntermediateField (rationalBase K t) Ω) ≤ L)
            (constantExtensionLineEquiv htK X)) :=
        congrArg (fun f => coordRingVal t (f (constantExtensionLineEquiv htK X))) hgL
      _ = t := (coe_constantExtensionLineEquiv htK X).trans (aeval_X t)
  apply parameterLineAlgHom_ext ht
  apply coordRingVal_injective t
  change s = _
  exact hst_eq.trans ((coe_constantExtensionLineEquiv ht X).trans (aeval_X t)).symm

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
