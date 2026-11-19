import Definitions.Def_TripodCanonicalHighHeightInputs
import Mathlib.Tactic.NormNum

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero

section IntValuation
variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]

omit [IsDedekindDomain R] [IsDedekindDomain S] in
lemma mem_comap_pow_iff (f : R →+* S) (hf : Function.Bijective f) (I : Ideal S) (a : R)
    (n : ℕ) : a ∈ (I.comap f) ^ n ↔ f a ∈ I ^ n := by
  let e := RingEquiv.ofBijective f hf
  have he : I.comap f = I.comap e := by
    ext x; rw [Ideal.mem_comap, Ideal.mem_comap, RingEquiv.coe_ofBijective]
  have hea : f a = e a := (RingEquiv.coe_ofBijective f hf).symm ▸ rfl
  rw [he, hea, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]

theorem intValuation_of_comap {v : HeightOneSpectrum S} {w : HeightOneSpectrum R} (f : R →+* S)
    (hf : Function.Bijective f) (hw : w.asIdeal = v.asIdeal.comap f) (a : R) :
    w.intValuation a = v.intValuation (f a) := by
  have key : ∀ n : ℕ, w.intValuation a ≤ exp (-(n : ℤ)) ↔
      v.intValuation (f a) ≤ exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      hw]
    exact mem_comap_pow_iff f hf v.asIdeal a n
  by_cases ha : a = 0
  · subst ha; simp
  have hfa : f a ≠ 0 := (map_ne_zero_iff f hf.injective).2 ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, w.intValuation a = exp (-(m : ℤ)) :=
    ⟨_, w.intValuation_if_neg ha⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, v.intValuation (f a) = exp (-(m' : ℤ)) :=
    ⟨_, v.intValuation_if_neg hfa⟩
  rw [hm, hm'] at key ⊢
  simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at key
  rw [le_antisymm ((key m).1 le_rfl) ((key m').2 le_rfl)]

theorem valuation_of_comap {K L : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra S L] [IsFractionRing S L] {v : HeightOneSpectrum S} {w : HeightOneSpectrum R}
    (f : R →+* S) (hf : Function.Bijective f) (hw : w.asIdeal = v.asIdeal.comap f)
    (φ : K →+* L) (hφ : ∀ r : R, φ (algebraMap R K r) = algebraMap S L (f r)) (x : K) :
    w.valuation K x = v.valuation L (φ x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have h3 : v.valuation L (algebraMap S L (f r)) = v.intValuation (f r) :=
    v.valuation_of_algebraMap (K := L) (f r)
  have h4 : v.valuation L (algebraMap S L (f s)) = v.intValuation (f s) :=
    v.valuation_of_algebraMap (K := L) (f s)
  change w.valuation K (IsLocalization.mk' K r s) = v.valuation L (φ (IsLocalization.mk' K r s))
  rw [HeightOneSpectrum.valuation_of_mk', IsFractionRing.mk'_eq_div, map_div₀, hφ, hφ, map_div₀,
    h3, h4, intValuation_of_comap f hf hw, intValuation_of_comap f hf hw]

end IntValuation

lemma toNNReal_congr {e e' : NNReal} (h : e = e') (he : e ≠ 0) (he' : e' ≠ 0) (x : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal he x = WithZeroMulInt.toNNReal he' x := by
  subst h; rfl

section MapEquiv
variable {k k' : Type*} [Field k] [NumberField k] [Field k'] [NumberField k']

noncomputable def FinitePlace.mapEquiv (e : k ≃+* k') : FinitePlace k ≃ FinitePlace k' :=
  FinitePlace.equivHeightOneSpectrum.trans
    ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).trans
      FinitePlace.equivHeightOneSpectrum.symm)

variable (e : k ≃+* k') (v : FinitePlace k)

lemma FinitePlace.mapEquiv_maximalIdeal :
    (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal =
      v.maximalIdeal.asIdeal.comap ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k) := by
  simp only [FinitePlace.mapEquiv, Equiv.trans_apply, FinitePlace.equivHeightOneSpectrum_apply,
    HeightOneSpectrum.equivOfRingEquiv_apply]
  exact congrArg HeightOneSpectrum.asIdeal (FinitePlace.maximalIdeal_mk _)

lemma FinitePlace.mapEquiv_valuation (x : k') :
    (FinitePlace.mapEquiv e v).maximalIdeal.valuation k' x =
      v.maximalIdeal.valuation k (e.symm x) :=
  valuation_of_comap ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k)
    (RingOfIntegers.mapRingEquiv e).symm.bijective (FinitePlace.mapEquiv_maximalIdeal e v)
    (e.symm : k' →+* k) (fun _ => rfl) x

lemma FinitePlace.mapEquiv_absNorm :
    Ideal.absNorm (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal =
      Ideal.absNorm v.maximalIdeal.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  have hIJ : v.maximalIdeal.asIdeal =
      (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal.map
        ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k) := by
    rw [FinitePlace.mapEquiv_maximalIdeal,
      Ideal.map_comap_of_surjective (f := ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k))
        (RingOfIntegers.mapRingEquiv e).symm.surjective]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv e).symm hIJ).toEquiv

lemma FinitePlace.mapEquiv_apply (x : k') :
    FinitePlace.mapEquiv e v x = v (e.symm x) := by
  rw [← FinitePlace.norm_embedding_eq, ← FinitePlace.norm_embedding_eq,
    FinitePlace.norm_embedding', FinitePlace.norm_embedding', FinitePlace.mapEquiv_valuation]
  congr 1
  refine toNNReal_congr ?_ _ _ _
  exact_mod_cast FinitePlace.mapEquiv_absNorm e v

end MapEquiv
end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField
open scoped Real

variable {T : Type*} [Field T] [NumberField T]

lemma finHeight_mapEquiv {T' : Type*} [Field T'] [NumberField T'] (e : T ≃+* T') (y : T) :
    finHeight (e y) = finHeight y := by
  unfold finHeight
  rw [← finsum_comp_equiv (FinitePlace.mapEquiv e)]
  refine finsum_congr fun v => ?_
  rw [FinitePlace.mapEquiv_apply, RingEquiv.symm_apply_apply]

end AbcAdaptation.Tripod
