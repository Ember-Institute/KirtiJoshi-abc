/-
Source: Pi1/Orbicurve/BaseChange.lean and Pi1/Orbicurve/SubfieldGalois.lean at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftConstantExtensionGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationInertia

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin Pointwise

universe u

noncomputable section

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω]
  [Algebra k Ω] [IsScalarTower k K Ω] {t : Ω}

attribute [local instance] fieldRingAction

section Base

omit [Field k] [Algebra k K] [Algebra k Ω] [IsScalarTower k K Ω] in
/-- The coordinate ring of the bottom field is the polynomial base ring. -/
def polynomialBaseToBottom (ht : Transcendental K t) :
    polynomialBase K t ≃ₐ[K] coordRing t (⊥ : IntermediateField (rationalBase K t) Ω) := by
  let B : IntermediateField (rationalBase K t) Ω := ⊥
  refine AlgEquiv.ofBijective (IsScalarTower.toAlgHom K (polynomialBase K t) (coordRing t B))
    ⟨fun a b hab => ?_, fun b => ?_⟩
  · exact Subtype.ext (congrArg (fun c : coordRing t B => ((c : B) : Ω)) hab)
  · have hb : ((b : B) : Ω) ∈ rationalBase K t := by
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp (b : B).2
      change (c : Ω) = ((b : B) : Ω) at hc
      exact hc ▸ c.2
    refine ⟨⟨b, mem_polynomialBase_of_isIntegral ht hb (isIntegral_of_mem_coordRing t b)⟩, ?_⟩
    exact Subtype.ext (Subtype.ext rfl)

omit [Field k] [Algebra k K] [Algebra k Ω] [IsScalarTower k K Ω] in
/-- The polynomial coordinates on the bottom normalization ring. -/
def constantExtensionLineEquiv (ht : Transcendental K t) :
    K[X] ≃ₐ[K] coordRing t (⊥ : IntermediateField (rationalBase K t) Ω) :=
  (Polynomial.algEquivOfTranscendental K t ht).trans (polynomialBaseToBottom ht)

omit [Field k] [Algebra k K] [Algebra k Ω] [IsScalarTower k K Ω] in
theorem coe_constantExtensionLineEquiv (ht : Transcendental K t) (p : K[X]) :
    (((constantExtensionLineEquiv ht p : coordRing t
      (⊥ : IntermediateField (rationalBase K t) Ω)) :
        (⊥ : IntermediateField (rationalBase K t) Ω)) : Ω) = aeval t p := by
  change ((Polynomial.algEquivOfTranscendental K t ht p : polynomialBase K t) : Ω) = _
  rw [Polynomial.algEquivOfTranscendental_apply, ← Subalgebra.aeval_coe]

end Base

section Unramified

open UniqueFactorizationMonoid

/-- In a Dedekind domain, `p S ⊆ P ^ n` bounds the ramification index from below. -/
private lemma le_ramificationIdx'_of_le_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain S] {p : Ideal R} {P : Ideal S} (hp0 : p.map (algebraMap R S) ≠ ⊥)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) {n : ℕ} (h : p.map (algebraMap R S) ≤ P ^ n) :
    n ≤ p.ramificationIdx' P := by
  classical
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]
  have hdvd : P ^ n ∣ p.map (algebraMap R S) := Ideal.dvd_iff_le.mpr h
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0,
    normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
    Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le] at hdvd
  exact hdvd

/-- An element of the lower prime whose image lies outside the square of the upper prime gives
the ramification index bound in this square of rings. -/
private lemma ramificationIdx_le_of_square {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [IsDomain R] [IsDomain R'] [IsDedekindDomain S] [IsDedekindDomain S']
    [IsPrincipalIdealRing R'] [Algebra R S] [Algebra R' S'] [Module.IsTorsionFree R S]
    [Module.IsTorsionFree R' S'] [Algebra.IsIntegral R S]
    (α : R →+* R') (β : S →+* S')
    (hcomm : ∀ r, β (algebraMap R S r) = algebraMap R' S' (α r))
    (u' : Ideal S') [hu' : u'.IsPrime] (hu : u'.comap β ≠ ⊥)
    (hsq : ∃ a ∈ (u'.comap β).under R, α a ∉ (u'.under R') ^ 2) :
    (u'.comap β).ramificationIdx R ≤ u'.ramificationIdx R' := by
  classical
  set u := u'.comap β
  haveI : u.IsPrime := Ideal.comap_isPrime β u'
  set p := u.under R
  set p' := u'.under R'
  obtain ⟨a, ha, hap⟩ := hsq
  have hau : algebraMap R S a ∈ u := ha
  have hap' : α a ∈ p' := by
    change algebraMap R' S' (α a) ∈ u'
    rw [← hcomm]; exact hau
  have hp'0 : p' ≠ ⊥ := by
    rintro h
    apply hap
    rw [h] at hap' ⊢
    rw [Ideal.mem_bot] at hap'
    rw [hap']; exact zero_mem _
  have hu'0 : u' ≠ ⊥ := by
    rintro rfl
    apply hp'0
    rw [eq_bot_iff]
    intro x hx
    have : algebraMap R' S' x = 0 := (Ideal.mem_bot).mp hx
    exact (Ideal.mem_bot).mpr ((Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
      (this.trans (map_zero _).symm))
  have hp0 : p ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hu
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  haveI : u.LiesOver p := ⟨rfl⟩
  haveI : u'.LiesOver p' := ⟨rfl⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx p u hp0,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p' u' hp'0]
  set e := p.ramificationIdx' u
  -- `β(a) ∈ u'^e`
  have h1 : algebraMap R S a ∈ u ^ e :=
    Ideal.le_pow_ramificationIdx' (p := p) (P := u) (Ideal.mem_map_of_mem _ ha)
  have h2 : algebraMap R' S' (α a) ∈ u' ^ e := by
    rw [← hcomm]
    have : Ideal.map β (u ^ e) ≤ u' ^ e := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr le_rfl) e
    exact this (Ideal.mem_map_of_mem β h1)
  -- `α(a) = g r` with `p' = (g)`, `r ∉ p'`
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal p').principal
  have hg' : p' = Ideal.span {g} := hg
  have hga : g ∣ α a := by
    rw [← Ideal.mem_span_singleton, ← hg']; exact hap'
  obtain ⟨r, hr⟩ := hga
  have hr' : r ∉ p' := by
    intro hrp
    apply hap
    rw [hg', Ideal.span_singleton_pow, Ideal.mem_span_singleton, hr, pow_two]
    rw [hg', Ideal.mem_span_singleton] at hrp
    exact mul_dvd_mul_left g hrp
  have h3 : algebraMap R' S' g ∈ u' ^ e := by
    have : algebraMap R' S' r * algebraMap R' S' g ∈ u' ^ e := by
      rw [← map_mul, mul_comm, ← hr]; exact h2
    exact (Ideal.IsPrime.mul_mem_pow u' this).resolve_left hr'
  have hmap : p'.map (algebraMap R' S') ≤ u' ^ e := by
    rw [hg', Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact h3
  have hmap0 : p'.map (algebraMap R' S') ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp'0
  exact le_ramificationIdx'_of_le_pow hmap0 hu' hu'0 hmap

end Unramified

section Line

lemma constantExtensionMap_constantExtensionLineEquiv (htk : Transcendental k t) (htK : Transcendental K t) (q : k[X]) :
    constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t)) (constantExtensionLineEquiv htk q) = constantExtensionLineEquiv htK (q.map (algebraMap k K)) := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_constantExtensionMap, coe_constantExtensionLineEquiv, coe_constantExtensionLineEquiv, Polynomial.aeval_map_algebraMap]

/-- **`k[t] → K[t]` is unramified** (characteristic `0`): for a nonzero prime `v'` of `K[t]` over
the nonzero prime `v` of `k[t]`, some element of `v` is not in `v'²`. -/
private lemma exists_mem_not_mem_sq [CharZero k] (htk : Transcendental k t) (htK : Transcendental K t)
    (v' : Ideal (coordRing t (⊥ : IntermediateField (rationalBase K t) Ω))) [hv' : v'.IsPrime]
    (hv0 : v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t))) ≠ ⊥) :
    ∃ a ∈ v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t))), constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t)) a ∉ v' ^ 2 := by
  classical
  set ek := constantExtensionLineEquiv (Ω := Ω) htk
  set eK := constantExtensionLineEquiv (Ω := Ω) htK
  set v := v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t)))
  haveI : v.IsPrime := Ideal.comap_isPrime _ _
  let Q : Ideal k[X] := v.comap ek.toRingEquiv.toRingHom
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hv0
    rw [eq_bot_iff]
    intro x hx
    have : ek.symm x ∈ Q := by
      change ek (ek.symm x) ∈ v
      rw [AlgEquiv.apply_symm_apply]; exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← ek.apply_symm_apply x, this, map_zero]
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal Q).principal
  have hQπ : Q = Ideal.span {π} := hπ
  have hπprime : Prime π := by
    rw [← Ideal.span_singleton_prime (fun h => hQ0 (by rw [hQπ, h, Ideal.span_singleton_eq_bot.mpr rfl])),
      ← hQπ]
    infer_instance
  have hsq : Squarefree (π.map (algebraMap k K)) :=
    ((hπprime.irreducible.separable).map).squarefree
  refine ⟨ek π, ?_, ?_⟩
  · change π ∈ Q
    rw [hQπ]; exact Ideal.mem_span_singleton_self π
  · intro hmem
    rw [constantExtensionMap_constantExtensionLineEquiv htk htK] at hmem
    let Q' : Ideal K[X] := v'.comap eK.toRingEquiv.toRingHom
    haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal Q').principal
    have hQ'q : Q' = Ideal.span {q} := hq
    have hv'q : v' = Ideal.span {eK q} := by
      ext x
      rw [Ideal.mem_span_singleton, ← eK.apply_symm_apply x, map_dvd_iff eK]
      exact (show eK.symm x ∈ Q' ↔ _ by rw [hQ'q, Ideal.mem_span_singleton])
    rw [hv'q, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow, map_dvd_iff eK,
      pow_two] at hmem
    have hunit := hsq q hmem
    apply (show Q' ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance)
    rw [hQ'q, Ideal.span_singleton_eq_top]
    exact hunit

end Line

private lemma fixSub_bot {T : Type u} [Field T] [Algebra T Ω]
    (N : IntermediateField (rationalBase T t) Ω) : fixSub N ⊥ = ⊤ := by
  refine eq_top_iff.mpr fun σ _ x hx => ?_
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hx
  have : x = algebraMap (rationalBase T t) N c := Subtype.ext hc.symm
  rw [this, AlgEquiv.commutes]

section Inertia

variable {N : IntermediateField (rationalBase k t) Ω} {N' : IntermediateField (rationalBase K t) Ω}
  (hN : ∀ x ∈ N, x ∈ N') [FiniteDimensional (rationalBase k t) N]
  [CharZero k] (htK : Transcendental K t) [IsGalois (rationalBase k t) N]
  [FiniteDimensional (rationalBase K t) N'] [IsGalois (rationalBase K t) N']

private lemma isPrincipalIdealRing_coordRing_bot (ht : Transcendental K t) :
    IsPrincipalIdealRing (coordRing t (⊥ : IntermediateField (rationalBase K t) Ω)) :=
  IsPrincipalIdealRing.of_surjective (constantExtensionLineEquiv ht).toRingEquiv.toRingHom
    (constantExtensionLineEquiv ht).surjective

local notation "F₀" => (⊥ : IntermediateField (rationalBase k t) Ω)
local notation "F₀'" => (⊥ : IntermediateField (rationalBase K t) Ω)

include htK in
private lemma ramificationIdx_bot_le_of_constantExtension
    (u' : Ideal (coordRing t N')) [hu' : u'.IsMaximal]
    (hu : u'.comap (constantExtensionMap hN) ≠ ⊥) :
    (letI := ringMapAlgebra (bot_le : F₀ ≤ N)
     (u'.comap (constantExtensionMap hN)).ramificationIdx (coordRing t F₀)) ≤
      (letI := ringMapAlgebra (bot_le : F₀' ≤ N')
       u'.ramificationIdx (coordRing t F₀')) := by
  have htk : Transcendental k t := transcendental_of_constantExtension htK
  let h₀ : F₀ ≤ N := bot_le
  let h₀' : F₀' ≤ N' := bot_le
  let α : coordRing t F₀ →+* coordRing t F₀' :=
    constantExtensionMap (bot_mem_constantExtension (k := k) (K := K) (t := t))
  let β : coordRing t N →+* coordRing t N' := constantExtensionMap hN
  letI : Algebra (coordRing t F₀) (coordRing t N) := ringMapAlgebra h₀
  letI : Algebra (coordRing t F₀') (coordRing t N') := ringMapAlgebra h₀'
  letI : IsDedekindDomain (coordRing t N) := dedekindRing t htk N
  letI : IsDedekindDomain (coordRing t N') := dedekindRing t htK N'
  letI : IsPrincipalIdealRing (coordRing t F₀') := isPrincipalIdealRing_coordRing_bot htK
  letI : Module.IsTorsionFree (coordRing t F₀) (coordRing t N) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (ringMap_injective h₀)
  letI : Module.IsTorsionFree (coordRing t F₀') (coordRing t N') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (ringMap_injective h₀')
  letI : Algebra.IsIntegral (coordRing t F₀) (coordRing t N) := ⟨ringMap_isIntegral h₀⟩
  letI : u'.IsPrime := hu'.isPrime
  let u : Ideal (coordRing t N) := u'.comap β
  let v' : Ideal (coordRing t F₀') := u'.under (coordRing t F₀')
  letI : v'.IsPrime := Ideal.comap_isPrime _ _
  have hcomap : u.under (coordRing t F₀) = v'.comap α := rfl
  have hv0 : v'.comap α ≠ ⊥ := by
    rw [← hcomap]
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show u ≠ ⊥ from hu)
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  have hsq : ∃ a ∈ u.under (coordRing t F₀), α a ∉ v' ^ 2 := by
    rw [hcomap]
    exact exists_mem_not_mem_sq htk htK v' hv0
  change u.ramificationIdx (coordRing t F₀) ≤ u'.ramificationIdx (coordRing t F₀')
  exact ramificationIdx_le_of_square α β (fun _ => rfl) u' hu hsq

/-- The bottom normalization has inertia under the full Galois group. -/
private lemma ramificationIdx_bot_eq_card_inertia {T : Type u} [Field T] [Algebra T Ω]
    [CharZero T] {L : IntermediateField (rationalBase T t) Ω}
    [FiniteDimensional (rationalBase T t) L] [IsGalois (rationalBase T t) L]
    (ht : Transcendental T t) (w : Ideal (coordRing t L)) [w.IsMaximal] :
    (letI := ringMapAlgebra (bot_le : (⊥ : IntermediateField (rationalBase T t) Ω) ≤ L)
     w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase T t) Ω))) =
      Nat.card (w.inertia (L ≃ₐ[rationalBase T t] L)) := by
  simpa only [fixSub_bot, inf_top_eq] using
    (ramificationIdx_eq_card_inertia ht (bot_le : (⊥ : IntermediateField (rationalBase T t) Ω) ≤ L) w)

include htK in
/-- The inertia group at a nonzero contracted prime has cardinality at most the upper inertia group. -/
private lemma card_inertia_le (u' : Ideal (coordRing t N')) [hu' : u'.IsMaximal]
    (hu : u'.comap (constantExtensionMap hN) ≠ ⊥) :
    Nat.card ((u'.comap (constantExtensionMap hN)).inertia (N ≃ₐ[rationalBase k t] N)) ≤
      Nat.card (u'.inertia (N' ≃ₐ[rationalBase K t] N')) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have htk : Transcendental k t := transcendental_of_constantExtension htK
  let u : Ideal (coordRing t N) := u'.comap (constantExtensionMap hN)
  letI : u.IsPrime := Ideal.comap_isPrime _ _
  letI : IsDedekindDomain (coordRing t N) := dedekindRing t htk N
  letI : u.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (show u ≠ ⊥ from hu)
  exact (ramificationIdx_bot_eq_card_inertia htk u).ge.trans
    ((ramificationIdx_bot_le_of_constantExtension hN htK u' hu).trans
      (ramificationIdx_bot_eq_card_inertia htK u').le)

include htK in
/-- **Restriction identifies the inertia groups** `I_{u'} ≅ I_{u' ∩ N}` (for `u' ∩ N ≠ 0`). -/
private lemma map_constantExtensionRes_inertia (hN' : N' ≤ IntermediateField.adjoin (rationalBase K t) (N : Set Ω))
    (u' : Ideal (coordRing t N')) [u'.IsMaximal] (hu : u'.comap (constantExtensionMap hN) ≠ ⊥) :
    (u'.inertia (N' ≃ₐ[rationalBase K t] N')).map (constantExtensionRes hN) =
      (u'.comap (constantExtensionMap hN)).inertia (N ≃ₐ[rationalBase k t] N) := by
  have hle : (u'.inertia (N' ≃ₐ[rationalBase K t] N')).map (constantExtensionRes hN) ≤
      (u'.comap (constantExtensionMap hN)).inertia (N ≃ₐ[rationalBase k t] N) := by
    rintro _ ⟨σ', hσ', rfl⟩
    exact constantExtensionRes_mem_inertia hN u' σ' hσ'
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (constantExtensionRes_injective hN hN')]
  exact card_inertia_le hN htK u' hu

include htK in
private lemma card_inertia_inf_fixSub (hN' : N' ≤ IntermediateField.adjoin (rationalBase K t) (N : Set Ω))
    {F : IntermediateField (rationalBase k t) Ω} {F' : IntermediateField (rationalBase K t) Ω}
    (hFN : F ≤ N) (hF : ∀ x ∈ F, x ∈ F') (hF' : F' ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω))
    (u' : Ideal (coordRing t N')) [u'.IsMaximal] (hu : u'.comap (constantExtensionMap hN) ≠ ⊥) :
    Nat.card (u'.inertia (N' ≃ₐ[rationalBase K t] N') ⊓ fixSub N' F' : Subgroup _) =
      Nat.card ((u'.comap (constantExtensionMap hN)).inertia (N ≃ₐ[rationalBase k t] N) ⊓ fixSub N F : Subgroup _) := by
  rw [← Subgroup.card_map_of_injective (constantExtensionRes_injective hN hN')]
  have hmap : (u'.inertia (N' ≃ₐ[rationalBase K t] N') ⊓ fixSub N' F' : Subgroup _).map (constantExtensionRes hN) =
      (u'.comap (constantExtensionMap hN)).inertia (N ≃ₐ[rationalBase k t] N) ⊓ fixSub N F := by
    rw [← map_constantExtensionRes_inertia hN htK hN' u' hu]
    ext τ
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨σ', ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨σ', h1, rfl⟩, (constantExtensionRes_mem_fixSub hN hFN hF hF' σ').mp h2⟩
    · rintro ⟨⟨σ', h1, rfl⟩, h2⟩
      exact ⟨σ', ⟨h1, (constantExtensionRes_mem_fixSub hN hFN hF hF' σ').mpr h2⟩, rfl⟩
  rw [hmap]

end Inertia

section Compare

variable [IsAlgClosed Ω] [CharZero k]
variable {F L N : IntermediateField (rationalBase k t) Ω}
variable [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N]

local notation "G" => (N ≃ₐ[rationalBase k t] N)

omit [IsAlgClosed Ω] in
private theorem ramificationIdx_mul_card_inertia (ht : Transcendental k t)
    (hFL : F ≤ L) (hLN : L ≤ N) (P : Ideal (coordRing t N)) [P.IsMaximal] :
    (letI := ringMapAlgebra hFL; (P.comap (ringMap hLN)).ramificationIdx (coordRing t F)) *
        Nat.card ((P.inertia G) ⊓ fixSub N L : Subgroup G) =
      Nat.card ((P.inertia G) ⊓ fixSub N F : Subgroup G) := by
  letI : FiniteDimensional (rationalBase k t) L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLN).toLinearMap
      (IntermediateField.inclusion hLN).injective
  letI : Algebra.IsSeparable (rationalBase k t) L :=
    Algebra.IsSeparable.of_algHom (F := rationalBase k t) (E := L) (E' := N)
      (IntermediateField.inclusion hLN)
  letI := dedekindRing t ht L
  have h := ramificationIdx_comp (ringMap hFL).toRingHom
    (ringMap hLN).toRingHom (ringMap_injective hLN) P
  have hcomp : (ringMap hLN).toRingHom.comp (ringMap hFL).toRingHom =
      (ringMap (hFL.trans hLN)).toRingHom := RingHom.ext fun _ => rfl
  rw [hcomp] at h
  rw [← ramificationIdx_eq_card_inertia ht hLN P,
    ← ramificationIdx_eq_card_inertia ht (hFL.trans hLN) P]
  exact h.symm

end Compare

variable [IsAlgClosed Ω] [CharZero k]

/-- Ramification indices agree at a closed prime whose contraction is nonzero. -/
theorem ramificationIdx_constantExtension_eq (htK : Transcendental K t)
    {F₁ F₂ : IntermediateField (rationalBase k t) Ω}
    {F₁' F₂' : IntermediateField (rationalBase K t) Ω}
    [FiniteDimensional (rationalBase k t) F₂] (h : F₁ ≤ F₂) (h' : F₁' ≤ F₂')
    (h₁ : ∀ x ∈ F₁, x ∈ F₁') (h₂ : ∀ x ∈ F₂, x ∈ F₂')
    (h₁' : F₁' ≤ IntermediateField.adjoin (rationalBase K t) (F₁ : Set Ω))
    (h₂' : F₂' ≤ IntermediateField.adjoin (rationalBase K t) (F₂ : Set Ω))
    (w' : Ideal (coordRing t F₂')) [hw' : w'.IsMaximal]
    (hw₀ : w'.comap (constantExtensionMap h₂) ≠ ⊥) :
    (letI := ringMapAlgebra h'; w'.ramificationIdx (coordRing t F₁')) =
      (letI := ringMapAlgebra h; (w'.comap (constantExtensionMap h₂)).ramificationIdx
        (coordRing t F₁)) := by
  have htk : Transcendental k t := transcendental_of_constantExtension htK
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
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
  set u := u'.comap (constantExtensionMap hNN')
  letI : u.IsPrime := Ideal.comap_isPrime _ _
  have hwu : w'.comap (constantExtensionMap h₂) = u.comap (ringMap hF₂N) := by
    rw [← hu'w]
    ext x
    exact Iff.rfl
  have hune : u ≠ ⊥ := by
    intro hz
    apply hw₀
    rw [hwu, hz]
    exact Ideal.comap_bot_of_injective _ (ringMap_injective hF₂N)
  letI := dedekindRing t htk N
  haveI : u.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hune
  have hc' := ramificationIdx_mul_card_inertia htK h' hF₂'N' u'
  have hc := ramificationIdx_mul_card_inertia htk h hF₂N u
  rw [hu'w] at hc'
  rw [← hwu] at hc
  have h₁card := card_inertia_inf_fixSub hNN' htK (le_of_eq hN') (h.trans hF₂N) h₁ h₁' u' hune
  have h₂card := card_inertia_inf_fixSub hNN' htK (le_of_eq hN') hF₂N h₂ h₂' u' hune
  rw [h₁card, h₂card, ← hc] at hc'
  have hpos : 0 < Nat.card (u.inertia (N ≃ₐ[rationalBase k t] N) ⊓ fixSub N F₂ : Subgroup _) :=
    Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos hc'

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
