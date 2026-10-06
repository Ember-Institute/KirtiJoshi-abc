import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.NumberTheory.RamificationInertia.Basic

namespace JoshiTeich.Prologue.Arithmetic

open IsDedekindDomain
open scoped NumberField

universe uK uL

/-!
source-id: IUT-COR312-FINITE-PLACE-BASE-CHANGE
source: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean`,
`sum_localDeg_liesOver` (245--276), together with its relative ramification and
inertia identities (171--217).
fidelity: port of the finite-place ideal calculation to the mathlib
`Ideal.LiesOver` carrier; no IUT-specific `FinitePlace` namespace is imported.
boundary: Prologue/Core

This is the arithmetic identity needed by the IUT q-root accounting.  It says
that the sum of `e_v f_v` over all places of `L` above a fixed place of `K` is
`[L : K] e_w f_w`.  It is independent of any Tate parameter or theta-volume
construction.
-/

section Extension

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev relRamIdx (v : NumberField.FinitePlace L)
    (w : NumberField.FinitePlace K) : ℕ :=
  w.maximalIdeal.asIdeal.ramificationIdx' v.maximalIdeal.asIdeal

noncomputable abbrev relInertDeg (v : NumberField.FinitePlace L)
    (w : NumberField.FinitePlace K) : ℕ :=
  w.maximalIdeal.asIdeal.inertiaDeg' v.maximalIdeal.asIdeal

variable {v : NumberField.FinitePlace L} {w : NumberField.FinitePlace K}

lemma under_int_eq (v : NumberField.FinitePlace K) :
    v.maximalIdeal.asIdeal.under ℤ = Ideal.span {(residueChar v : ℤ)} := by
  set P := v.maximalIdeal.asIdeal
  have hp : (residueChar v).Prime := residueChar_prime v
  haveI : CharP (𝓞 K ⧸ P) (residueChar v) := ringChar.charP _
  have hmem : (residueChar v : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.natCast_mem_of_charP_quotient (residueChar v) P
  have hle : Ideal.span {(residueChar v : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  haveI hprime : (Ideal.span {(residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  haveI hmax : (Ideal.span {(residueChar v : ℤ)}).IsMaximal :=
    IsPrime.to_maximal_ideal (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero)
  exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm

lemma under_int_ne_bot (v : NumberField.FinitePlace K) :
    v.maximalIdeal.asIdeal.under ℤ ≠ ⊥ := by
  rw [under_int_eq, ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast (residueChar_prime v).ne_zero

lemma under_int_isMaximal (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.asIdeal.under ℤ).IsMaximal := by
  have hp : (residueChar v).Prime := residueChar_prime v
  rw [under_int_eq]
  haveI hprime : (Ideal.span {(residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  exact IsPrime.to_maximal_ideal (by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero)

lemma under_int_eq_under_int
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    v.maximalIdeal.asIdeal.under ℤ = w.maximalIdeal.asIdeal.under ℤ := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  rw [← Ideal.under_under (B := 𝓞 K) v.maximalIdeal.asIdeal,
    ← Ideal.over_def v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal]

lemma relRamIdx_ne_zero
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    relRamIdx v w ≠ 0 := by
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    v.maximalIdeal.asIdeal w.maximalIdeal.ne_bot

lemma ramIdx_eq_mul
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    ramIdx v = ramIdx w * relRamIdx v w := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  have hp : v.maximalIdeal.asIdeal.under ℤ ≠ ⊥ := by
    exact under_int_ne_bot v
  haveI : w.maximalIdeal.asIdeal.LiesOver
      (v.maximalIdeal.asIdeal.under ℤ) :=
    Ideal.LiesOver.tower_bot v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal _
  have h1 : ramIdx v =
      (v.maximalIdeal.asIdeal.under ℤ).ramificationIdx'
        v.maximalIdeal.asIdeal :=
    (Ideal.ramificationIdx'_eq_ramificationIdx _
      v.maximalIdeal.asIdeal hp).symm
  have h2 : ramIdx w =
      (v.maximalIdeal.asIdeal.under ℤ).ramificationIdx'
        w.maximalIdeal.asIdeal := by
    have h := (Ideal.ramificationIdx'_eq_ramificationIdx
      (w.maximalIdeal.asIdeal.under ℤ) w.maximalIdeal.asIdeal (by
        exact under_int_ne_bot w)).symm
    rw [under_int_eq_under_int hvw]
    exact h
  rw [h1, h2]
  exact Ideal.ramificationIdx'_algebra_tower' _
    w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal

lemma inertDeg_eq_mul
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    inertDeg v = inertDeg w * relInertDeg v w := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  haveI : w.maximalIdeal.asIdeal.LiesOver
      (v.maximalIdeal.asIdeal.under ℤ) :=
    Ideal.LiesOver.tower_bot v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal _
  have h1 : inertDeg v =
      (v.maximalIdeal.asIdeal.under ℤ).inertiaDeg'
        v.maximalIdeal.asIdeal :=
    (Ideal.inertiaDeg'_eq_inertiaDeg _ v.maximalIdeal.asIdeal).symm
  have h2 : inertDeg w =
      (v.maximalIdeal.asIdeal.under ℤ).inertiaDeg'
        w.maximalIdeal.asIdeal := by
    have h := (Ideal.inertiaDeg'_eq_inertiaDeg
      (w.maximalIdeal.asIdeal.under ℤ) w.maximalIdeal.asIdeal).symm
    rw [under_int_eq_under_int hvw]
    exact h
  rw [h1, h2]
  exact Ideal.inertiaDeg'_algebra_tower _
    w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal

lemma localDeg_eq_mul
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    localDeg v = localDeg w * (relRamIdx v w * relInertDeg v w) := by
  unfold localDeg
  rw [ramIdx_eq_mul hvw, inertDeg_eq_mul hvw]
  ring

end Extension

section Sum

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L] [Algebra K L]

theorem sum_localDeg_liesOver (w : NumberField.FinitePlace K)
    (s : Finset (NumberField.FinitePlace L))
    (hs : ∀ v, v ∈ s ↔
      Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    ∑ v ∈ s, localDeg v = Module.finrank K L * localDeg w := by
  classical
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  have hp0 : w.maximalIdeal.asIdeal ≠ ⊥ := w.maximalIdeal.ne_bot
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) K L hp0
    (p := w.maximalIdeal.asIdeal)
  have hbij : ∑ v ∈ s, (relRamIdx v w * relInertDeg v w) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset
        w.maximalIdeal.asIdeal (𝓞 L),
        w.maximalIdeal.asIdeal.ramificationIdx' P *
          w.maximalIdeal.asIdeal.inertiaDeg' P := by
    refine Finset.sum_bij (fun v _ => v.maximalIdeal.asIdeal) ?_ ?_ ?_ ?_
    · intro v hv
      haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal :=
        (hs v).mp hv
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).mpr
        ⟨inferInstance, inferInstance⟩
    · intro v₁ _ v₂ _ h
      exact NumberField.FinitePlace.maximalIdeal_injective
        (HeightOneSpectrum.ext h)
    · intro P hP
      obtain ⟨hprime, hover⟩ :=
        (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).mp hP
      have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
      refine ⟨NumberField.FinitePlace.mk ⟨P, hprime, hne⟩, ?_, ?_⟩
      · rw [hs]
        rw [NumberField.FinitePlace.maximalIdeal_mk]
        exact hover
      · rw [NumberField.FinitePlace.maximalIdeal_mk]
    · intro v _
      rfl
  have h : ∀ v ∈ s, localDeg v =
      localDeg w * (relRamIdx v w * relInertDeg v w) :=
    fun v hv => localDeg_eq_mul (v := v) (w := w) ((hs v).mp hv)
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, hbij, hsum, mul_comm]

end Sum

section RationalFiber

variable {K : Type uK} [Field K] [NumberField K]

/-!
The `iut` local theory uses the exact local-degree identity over a rational prime,
not only the resulting inequality.  The finite-place version below keeps the
same statement on the frozen mathlib carrier.
-/

theorem sum_localDeg (p : ℕ) (hp : p.Prime)
    [Fintype {w : NumberField.FinitePlace K // residueChar w = p}] :
    ∑ w : {w : NumberField.FinitePlace K // residueChar w = p}, localDeg w.1 =
      Module.finrank ℚ K := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hP0 : P ≠ ⊥ := by
    rw [hP, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI hmax : P.IsMaximal := by
    haveI hprime : P.IsPrime := by
      rw [hP]
      exact (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp)
    exact IsPrime.to_maximal_ideal hP0
  have hsum :
      ∑ Q ∈ IsDedekindDomain.primesOverFinset P (𝓞 K),
          Q.ramificationIdx ℤ * Q.inertiaDeg ℤ = Module.finrank ℚ K := by
    have hsum0 := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K)
    calc
      ∑ Q ∈ IsDedekindDomain.primesOverFinset P (𝓞 K),
          Q.ramificationIdx ℤ * Q.inertiaDeg ℤ =
          ∑ Q : P.primesOver (𝓞 K),
            Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ := by
        symm
        refine Finset.sum_bij (fun Q _ => Q.1) ?_ ?_ ?_ ?_
        · intro Q _
          exact (IsDedekindDomain.mem_primesOverFinset_iff hP0 (𝓞 K)).mpr Q.2
        · intro Q₁ _ Q₂ _ hQ
          exact Subtype.ext hQ
        · intro Q hQ
          have hQ' :=
            (IsDedekindDomain.mem_primesOverFinset_iff hP0 (𝓞 K)).mp hQ
          exact ⟨⟨Q, hQ'⟩, Finset.mem_univ _, rfl⟩
        · intro Q _
          rfl
      _ = Module.finrank ℚ K := by
        simpa only [NumberField.RingOfIntegers.rank] using hsum0
  rw [← hsum]
  refine Finset.sum_bij (fun w _ => w.1.maximalIdeal.asIdeal) ?_ ?_ ?_ ?_
  · intro w _
    haveI : w.1.maximalIdeal.asIdeal.LiesOver P := by
      rw [hP]
      simpa only [w.2] using residueChar_liesOver w.1
    exact (IsDedekindDomain.mem_primesOverFinset_iff hP0 (𝓞 K)).mpr
      ⟨inferInstance, inferInstance⟩
  · intro w₁ _ w₂ _ h
    exact Subtype.ext (NumberField.FinitePlace.maximalIdeal_injective
      (IsDedekindDomain.HeightOneSpectrum.ext h))
  · intro Q hQ
    obtain ⟨hprime, hover⟩ :=
      (IsDedekindDomain.mem_primesOverFinset_iff hP0 (𝓞 K)).mp hQ
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hP0 Q
    let w : NumberField.FinitePlace K := NumberField.FinitePlace.mk ⟨Q, hprime, hne⟩
    haveI : w.maximalIdeal.asIdeal.LiesOver P := by
      simpa only [w, NumberField.FinitePlace.maximalIdeal_mk] using hover
    have hw : residueChar w = p := by
      have h1 := under_int_eq w
      rw [← Ideal.over_def w.maximalIdeal.asIdeal P, hP,
        Ideal.span_singleton_eq_span_singleton] at h1
      have h2 := Int.natAbs_eq_iff_associated.mpr h1
      simpa using h2.symm
    exact ⟨⟨w, hw⟩, Finset.mem_univ _, by
      change w.maximalIdeal.asIdeal = Q
      simp [w, NumberField.FinitePlace.maximalIdeal_mk]⟩
  · intro w _
    haveI : w.1.maximalIdeal.asIdeal.LiesOver P := by
      rw [hP]
      simpa only [w.2] using residueChar_liesOver w.1
    haveI : w.1.maximalIdeal.asIdeal.IsMaximal :=
      w.1.maximalIdeal.isPrime.isMaximal w.1.maximalIdeal.ne_bot
    have hunder : w.1.maximalIdeal.asIdeal.under ℤ = P := by
      rw [under_int_eq, w.2, hP]
    have hram : ramIdx w.1 = P.ramificationIdx' w.1.maximalIdeal.asIdeal := by
      have h := (Ideal.ramificationIdx'_eq_ramificationIdx _
        w.1.maximalIdeal.asIdeal (under_int_ne_bot w.1)).symm
      rwa [hunder] at h
    have hinert : inertDeg w.1 = P.inertiaDeg' w.1.maximalIdeal.asIdeal := by
      haveI : (w.1.maximalIdeal.asIdeal.under ℤ).IsMaximal :=
        under_int_isMaximal w.1
      have h := (Ideal.inertiaDeg'_eq_inertiaDeg
        (w.1.maximalIdeal.asIdeal.under ℤ) w.1.maximalIdeal.asIdeal).symm
      rwa [hunder] at h
    have hram' : P.ramificationIdx' w.1.maximalIdeal.asIdeal =
        w.1.maximalIdeal.asIdeal.ramificationIdx ℤ := by
      have h := Ideal.ramificationIdx'_eq_ramificationIdx
        (w.1.maximalIdeal.asIdeal.under ℤ) w.1.maximalIdeal.asIdeal
          (under_int_ne_bot w.1)
      rwa [hunder] at h
    have hinert' : P.inertiaDeg' w.1.maximalIdeal.asIdeal =
        w.1.maximalIdeal.asIdeal.inertiaDeg ℤ := by
      haveI : (w.1.maximalIdeal.asIdeal.under ℤ).IsMaximal :=
        under_int_isMaximal w.1
      have h := Ideal.inertiaDeg'_eq_inertiaDeg
        (w.1.maximalIdeal.asIdeal.under ℤ) w.1.maximalIdeal.asIdeal
      rwa [hunder] at h
    change ramIdx w.1 * inertDeg w.1 =
      w.1.maximalIdeal.asIdeal.ramificationIdx ℤ *
        w.1.maximalIdeal.asIdeal.inertiaDeg ℤ
    rw [hram, hinert, hram', hinert']

end RationalFiber

section PlaceUnder

variable {F : Type uK} [Field F] [NumberField F]
variable {L : Type uL} [Field L] [NumberField L] [Algebra F L]

/-!
The contraction of a finite place to the base number field is the canonical
place-under map used by the `iut` local accounting.  Keeping it here avoids
making Scene1 source carriers part of the arithmetic API.
-/

noncomputable def placeUnder (v : NumberField.FinitePlace L) :
    NumberField.FinitePlace F :=
  NumberField.FinitePlace.mk
    { asIdeal := v.maximalIdeal.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
          v.maximalIdeal.ne_bot
        exact Ideal.under_ne_bot_of_integral_mem hx0 hx
          (Algebra.IsIntegral.isIntegral x) }

lemma placeUnder_maximalIdeal (v : NumberField.FinitePlace L) :
    (placeUnder v).maximalIdeal.asIdeal =
      v.maximalIdeal.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) := by
  rw [placeUnder, NumberField.FinitePlace.maximalIdeal_mk]

lemma liesOver_placeUnder (v : NumberField.FinitePlace L) :
    Ideal.LiesOver v.maximalIdeal.asIdeal (placeUnder v).maximalIdeal.asIdeal := by
  exact ⟨by rw [placeUnder_maximalIdeal]⟩

lemma eq_placeUnder_of_liesOver {v : NumberField.FinitePlace L}
    {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    w = placeUnder v := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  change w.maximalIdeal = (placeUnder v).maximalIdeal
  apply IsDedekindDomain.HeightOneSpectrum.ext
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  rw [placeUnder_maximalIdeal]
  simpa only [Ideal.under_def] using
    (Ideal.over_def v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)

end PlaceUnder

section WeightedSum

variable {F : Type uK} [Field F] [NumberField F]
variable {L : Type uL} [Field L] [NumberField L] [Algebra F L]

/-!
This is the finite-place weighted-sum identity ported from
`refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`.  It is the arithmetic
accounting layer for a local order function: places not above the supplied
base support contribute zero, while each supported base place contributes its
residue-degree coefficient.  No Tate, q-root, or theta-volume datum occurs in
the statement.
-/

theorem sum_placeWeight_mul (p : ℕ)
    [Fintype {v : NumberField.FinitePlace L // residueChar v = p}]
    (B : Set (NumberField.FinitePlace F))
    (bad : Finset (NumberField.FinitePlace F)) (hbad : (↑bad : Set _) = B)
    (c : NumberField.FinitePlace F → ℝ)
    (o : NumberField.FinitePlace L → ℝ)
    (ho : ∀ v w, Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal →
      w ∈ B → o v = c w / ramIdx w)
    (ho0 : ∀ v, (∀ w ∈ B,
      ¬ Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) → o v = 0) :
    ∑ v : {v : NumberField.FinitePlace L // residueChar v = p},
        placeWeight v.1 * o v.1 =
      ∑ w ∈ bad.filter (fun w => residueChar w = p),
        (inertDeg w : ℝ) / Module.finrank ℚ F * c w := by
  classical
  have hmemB : ∀ w, w ∈ bad ↔ w ∈ B := fun w => by
    rw [← Finset.mem_coe, hbad]
  set s : Finset {v : NumberField.FinitePlace L // residueChar v = p} :=
    Finset.univ.filter (fun v => ∃ w ∈ B,
      Ideal.LiesOver v.1.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) with hs
  set t : Finset (NumberField.FinitePlace F) :=
    bad.filter (fun w => residueChar w = p) with ht
  have h1 :
      ∑ v : {v : NumberField.FinitePlace L // residueChar v = p},
          placeWeight v.1 * o v.1 =
        ∑ v ∈ s, placeWeight v.1 * o v.1 := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hne
    by_contra h
    push Not at h
    exact hne (by rw [ho0 v.1 h, mul_zero])
  have hmaps : ∀ v ∈ s, placeUnder v.1 ∈ t := by
    intro v hv
    obtain ⟨w, hwB, hvw⟩ := (Finset.mem_filter.mp hv).2
    have hw : w = placeUnder v.1 := eq_placeUnder_of_liesOver hvw
    rw [← hw]
    refine Finset.mem_filter.mpr ⟨(hmemB _).mpr hwB, ?_⟩
    rw [← residueChar_eq_of_liesOver hvw]
    exact v.2
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  obtain ⟨hwbad, hwp⟩ := Finset.mem_filter.mp hw
  have hwB : w ∈ B := (hmemB w).mp hwbad
  have hfib : ∀ v ∈ s.filter (fun v => placeUnder v.1 = w),
      Ideal.LiesOver v.1.maximalIdeal.asIdeal w.maximalIdeal.asIdeal := by
    intro v hv
    have h := (Finset.mem_filter.mp hv).2
    rw [← h]
    exact liesOver_placeUnder v.1
  have hsum :
      ∑ v ∈ s.filter (fun v => placeUnder v.1 = w),
          placeWeight v.1 * o v.1 =
        (c w / ramIdx w / Module.finrank ℚ L) *
          ∑ v ∈ s.filter (fun v => placeUnder v.1 = w),
            (localDeg v.1 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [ho v.1 w (hfib v hv) hwB]
    unfold placeWeight
    ring
  have hS :
      ∑ v ∈ (s.filter (fun v => placeUnder v.1 = w)).map
          (Function.Embedding.subtype _), localDeg v =
        Module.finrank F L * localDeg w := by
    apply sum_localDeg_liesOver w
    intro v
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hfib u hu
    · intro hvw
      refine ⟨⟨v, by rw [residueChar_eq_of_liesOver hvw, hwp]⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, w, hwB, hvw⟩, (eq_placeUnder_of_liesOver hvw).symm⟩
  rw [Finset.sum_map] at hS
  simp only [Function.Embedding.coe_subtype] at hS
  rw [hsum, ← Nat.cast_sum, hS]
  have hFL : (Module.finrank ℚ L : ℝ) =
      Module.finrank ℚ F * Module.finrank F L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F L).symm
  have he : (ramIdx w : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos w).ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hL : (Module.finrank F L : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  unfold localDeg
  rw [hFL]
  push_cast
  field_simp

end WeightedSum

end JoshiTeich.Prologue.Arithmetic
