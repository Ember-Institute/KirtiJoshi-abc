import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlaceSource
import Mathlib.NumberTheory.RamificationInertia.Valuation

namespace JoshiTeich.Act1Scene1

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero NumberField Valued

universe u uΓ

noncomputable section

/-!
source-id: IUT-COR312-COMPLETION-MAP
source: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean`,
especially `completionMapPow`, `adicCompletionMapPow`, `embedCompletion`,
`embedCompletion_embedding`, and `valued_embedCompletion`; valuation transfer is
the corresponding theorem in `refer/iut/Iut/Cor312/ThetaData/ValuationTransfer.lean`.
fidelity: the port uses the local `Ideal.LiesOver` relation and the frozen
mathlib adic-completion carrier.  It constructs the comparison map from the
field inclusion and relative ramification index; it does not construct a real
`InitialThetaData`, `TateFamily`, or q-root.
boundary: Scene1/Derived
-/

section ValuationPower

variable {k K : Type u} [Field k] [Field K]
variable {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]

theorem iutValuedWithValMapPow
    (v : Valuation k Γ₀) (v' : Valuation K Γ₀) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v' (φ x) = v x ^ e) (x : WithVal v) :
    Valued.v (WithVal.map v v' φ x) = Valued.v x ^ e := by
  rw [WithVal.map_apply, WithVal.valued_toVal, hφ, WithVal.apply_ofVal]

theorem iutUniformContinuousWithValMapPow
    (v : Valuation k Γ₀) (v' : Valuation K Γ₀) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) :
    UniformContinuous (WithVal.map v v' φ) := by
  refine uniformContinuous_of_continuousAt_zero (WithVal.map v v' φ) ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨x₀, hx₀⟩ := hv (min (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) 1)
  have hmin : min (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) 1 ≠ 0 := by
    rw [ne_eq, min_eq_iff]
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hγ0 h
    · exact one_ne_zero h
  have hne : (Valued.v : Valuation (WithVal v) Γ₀).restrict
      (WithVal.toVal v x₀) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, WithVal.valued_toVal, hx₀]
    exact hmin
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hne, fun x hx => hγ ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff,
    WithVal.valued_toVal, hx₀, lt_min_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding,
    iutValuedWithValMapPow v v' φ e hφ]
  calc
    Valued.v x ^ e ≤ Valued.v x := pow_le_of_le_one zero_le hx.2.le he
    _ < _ := hx.1

noncomputable def iutCompletionMapPow
    (v : Valuation k Γ₀) (v' : Valuation K Γ₀) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) :
    v.Completion →+* v'.Completion :=
  UniformSpace.Completion.mapRingHom (WithVal.map v v' φ)
    (iutUniformContinuousWithValMapPow v v' φ e hφ he hv).continuous

theorem iutCompletionMapPow_coe'
    (v : Valuation k Γ₀) (v' : Valuation K Γ₀) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) (x : WithVal v) :
    iutCompletionMapPow v v' φ e hφ he hv (x : v.Completion) =
      (WithVal.map v v' φ x : v'.Completion) := by
  exact UniformSpace.Completion.mapRingHom_coe _ x

theorem iutCompletionMapPow_coe
    (v : Valuation k Γ₀) (v' : Valuation K Γ₀) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) (x : k) :
    iutCompletionMapPow v v' φ e hφ he hv (x : v.Completion) =
      (φ x : v'.Completion) := by
  exact iutCompletionMapPow_coe' v v' φ e hφ he hv _

theorem iutContinuousCompletionMapPow
    (v : Valuation k Γ₀) (v' : Valuation K Γ₀) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) :
    Continuous (iutCompletionMapPow v v' φ e hφ he hv) :=
  UniformSpace.Completion.continuous_map

theorem iutValuedCompletionMapPow
    (v : Valuation k Γ₀) (v' : Valuation K Γ₀) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) (y : v.Completion) :
    Valued.v (iutCompletionMapPow v v' φ e hφ he hv y) = Valued.v y ^ e := by
  by_cases hy : y = 0
  · subst hy
    simp [zero_pow he]
  have hfy : iutCompletionMapPow v v' φ e hφ he hv y ≠ 0 :=
    (map_ne_zero _).2 hy
  have h1 : {z | Valued.v z = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have h2 : (iutCompletionMapPow v v' φ e hφ he hv) ⁻¹'
      {z | Valued.v z = Valued.v (iutCompletionMapPow v v' φ e hφ he hv y)} ∈ nhds y :=
    (iutContinuousCompletionMapPow v v' φ e hφ he hv).continuousAt.preimage_mem_nhds
      (Valued.locally_const ((Valuation.ne_zero_iff _).2 hfy))
  obtain ⟨t, hts, ht, hyt⟩ := mem_nhds_iff.1 (Filter.inter_mem h1 h2)
  obtain ⟨r, hr⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open ht ⟨y, hyt⟩
  obtain ⟨hr1, hr2⟩ := hts hr
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hr1 hr2
  rw [← hr1, ← hr2, iutCompletionMapPow_coe', Valued.valuedCompletion_apply,
    Valued.valuedCompletion_apply, iutValuedWithValMapPow v v' φ e hφ]

end ValuationPower

section Adic

variable {R S : Type u} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  {k K : Type u} [Field k] [Algebra R k] [IsFractionRing R k]
  [Field K] [Algebra S K] [IsFractionRing S K]

def iutAdicCompletionMapPow
    (v : HeightOneSpectrum R) (v' : HeightOneSpectrum S) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v'.valuation K (φ x) = v.valuation k x ^ e) (he : e ≠ 0) :
    v.adicCompletion k →+* v'.adicCompletion K :=
  let f : (v.valuation k).Completion →+* (v'.valuation K).Completion :=
    iutCompletionMapPow (v.valuation k) (v'.valuation K) φ e hφ he
      (v.valuation_surjective k)
  (HeightOneSpectrum.adicCompletion.equiv K v').symm.toRingHom.comp
    (f.comp (HeightOneSpectrum.adicCompletion.equiv k v).toRingHom)

theorem iutAdicCompletionMapPow_coe
    (v : HeightOneSpectrum R) (v' : HeightOneSpectrum S) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v'.valuation K (φ x) = v.valuation k x ^ e) (he : e ≠ 0) (x : k) :
    iutAdicCompletionMapPow v v' φ e hφ he (x : v.adicCompletion k) =
      (φ x : v'.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  exact iutCompletionMapPow_coe (v.valuation k) (v'.valuation K) φ e hφ he
    (v.valuation_surjective k) x

theorem iutContinuousAdicCompletionMapPow
    (v : HeightOneSpectrum R) (v' : HeightOneSpectrum S) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v'.valuation K (φ x) = v.valuation k x ^ e) (he : e ≠ 0) :
    Continuous (iutAdicCompletionMapPow v v' φ e hφ he) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v').comp
    ((iutContinuousCompletionMapPow (v.valuation k) (v'.valuation K) φ e hφ he
      (v.valuation_surjective k)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion k v))

theorem iutValuedAdicCompletionMapPow
    (v : HeightOneSpectrum R) (v' : HeightOneSpectrum S) (φ : k →+* K) (e : ℕ)
    (hφ : ∀ x, v'.valuation K (φ x) = v.valuation k x ^ e) (he : e ≠ 0)
    (y : v.adicCompletion k) :
    Valued.v (iutAdicCompletionMapPow v v' φ e hφ he y) = Valued.v y ^ e := by
  exact iutValuedCompletionMapPow _ _ _ _ hφ he (v.valuation_surjective k)
    y.toCompletion

end Adic

section Places

variable {F Kt : Type u} [Field F] [NumberField F]
  [Field Kt] [NumberField Kt] [Algebra F Kt]
  {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}

noncomputable abbrev iutRelativeRamificationIndex : ℕ :=
  w.maximalIdeal.asIdeal.ramificationIdx' v.maximalIdeal.asIdeal

lemma iutRelativeRamificationIndex_ne_zero
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    iutRelativeRamificationIndex (v := v) (w := w) ≠ 0 := by
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    v.maximalIdeal.asIdeal w.maximalIdeal.ne_bot

lemma iutValuation_algebraMap_eq_pow
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) (x : F) :
    v.maximalIdeal.valuation Kt (algebraMap F Kt x) =
      w.maximalIdeal.valuation F x ^ iutRelativeRamificationIndex (v := v) (w := w) := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  have h := (valuation_liesOver Kt w.maximalIdeal v.maximalIdeal x).symm
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
    w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal w.maximalIdeal.ne_bot] at h
  exact h

noncomputable def iutEmbedCompletion
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    w.maximalIdeal.adicCompletion F →+* v.maximalIdeal.adicCompletion Kt :=
  iutAdicCompletionMapPow w.maximalIdeal v.maximalIdeal (algebraMap F Kt)
    (iutRelativeRamificationIndex (v := v) (w := w))
    (iutValuation_algebraMap_eq_pow hvw)
    (iutRelativeRamificationIndex_ne_zero hvw)

theorem iutEmbedCompletion_embedding
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) (x : F) :
    iutEmbedCompletion hvw (NumberField.FinitePlace.embedding w.maximalIdeal x) =
      NumberField.FinitePlace.embedding v.maximalIdeal (algebraMap F Kt x) := by
  exact iutAdicCompletionMapPow_coe _ _ _ _
    (iutValuation_algebraMap_eq_pow hvw) _ x

theorem iutContinuousEmbedCompletion
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    Continuous (iutEmbedCompletion hvw) :=
  iutContinuousAdicCompletionMapPow _ _ _ _
    (iutValuation_algebraMap_eq_pow hvw)
    (iutRelativeRamificationIndex_ne_zero hvw)

theorem iutValuedEmbedCompletion
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (y : w.maximalIdeal.adicCompletion F) :
    Valued.v (iutEmbedCompletion hvw y) =
      Valued.v y ^ iutRelativeRamificationIndex (v := v) (w := w) :=
  iutValuedAdicCompletionMapPow _ _ _ _
    (iutValuation_algebraMap_eq_pow hvw)
    (iutRelativeRamificationIndex_ne_zero hvw) y

theorem iutEmbedCompletion_norm_lt_one_iff
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (y : w.maximalIdeal.adicCompletion F) :
    ‖iutEmbedCompletion hvw y‖ < 1 ↔ ‖y‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff,
    Valued.toNormedField.norm_lt_one_iff,
    iutValuedEmbedCompletion hvw]
  exact pow_lt_one_iff_of_nonneg zero_le
    (iutRelativeRamificationIndex_ne_zero hvw)

end Places

namespace IutTorsionQRootSource

variable {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
variable [Algebra F Kt] {ell : ℕ} {B : IutBaseQPilotSource F ell}

/-!
The reference source does not treat the comparison of completions as an
uninterpreted field: it is the extension of `F → Kt` at a place above the
base place.  This constructor consumes that canonical map, leaving only the
q-root and its power equation as local source obligations.
-/

noncomputable def ofOverBaseBadWithCanonicalCompletionMap
    (B : IutBaseQPilotSource F ell)
    (qroot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (qroot_ne_zero : ∀ v, qroot v ≠ 0)
    (qroot_pow_eq : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      qroot v ^ (2 * ell) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v))) :
    IutTorsionQRootSource F Kt ell B :=
  IutTorsionQRootSource.ofOverBaseBad B qroot qroot_ne_zero
    (fun v => iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)) qroot_pow_eq

lemma ofOverBaseBadWithCanonicalCompletionMap_badFinset
    (B : IutBaseQPilotSource F ell)
    (qroot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (qroot_ne_zero : ∀ v, qroot v ≠ 0)
    (qroot_pow_eq : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      qroot v ^ (2 * ell) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v))) :
    (ofOverBaseBadWithCanonicalCompletionMap B qroot qroot_ne_zero qroot_pow_eq).badFinset =
      iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces B.badPlaces_finite :=
  rfl

lemma canonical_qroot_valued_pow_eq
    (B : IutBaseQPilotSource F ell)
    (qroot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (qroot_pow_eq : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      qroot v ^ (2 * ell) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v)))
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    Valued.v (qroot v) ^ (2 * ell) =
      Valued.v (B.tateParameter (basePlaceOf (B := B) v)) ^
        iutRelativeRamificationIndex
          (v := v.1) (w := (basePlaceOf (B := B) v).1) := by
  simpa only [map_pow, iutValuedEmbedCompletion] using
    congrArg Valued.v (qroot_pow_eq v)

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
