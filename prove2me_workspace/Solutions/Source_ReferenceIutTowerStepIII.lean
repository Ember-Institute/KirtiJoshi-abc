/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/StepIII.lean
-/
import Solutions.Source_ReferenceIutTowerDifferentArithmetic
import Solutions.Source_FermatBelyiDifferentAccounting
import Solutions.Source_SL2ImageRangeCardinality
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain
open Tripod.Fermat.Proper.ConductorExtensionSource
  (placesOver mem_placesOver sum_placesOver_mul_eq_finrank
    primeSupport mem_primeSupport log_absNorm_eq_finsum)
open scoped BigOperators Classical

universe u

section FinitePlaces

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

private lemma placesOver_pairwiseDisjoint (s : Finset (FinitePlace k)) :
    (s : Set (FinitePlace k)).PairwiseDisjoint (placesOver K) := by
  intro w _ w' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro v hv hv'
  have h : FinitePlace.LiesOver v w := mem_placesOver.mp hv
  have h' : FinitePlace.LiesOver v w' := mem_placesOver.mp hv'
  exact hne ((Tripod.placeUnder_eq_of_liesOver_place h).symm.trans
    (Tripod.placeUnder_eq_of_liesOver_place h'))

private lemma relRamIdx_eq_of_isGalois [IsGalois k K] {v v' : FinitePlace K}
    {w : FinitePlace k} (h : FinitePlace.LiesOver v w) (h' : FinitePlace.LiesOver v' w) :
    Tripod.relRamIdx v w = Tripod.relRamIdx v' w := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := h
  haveI : v'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := h'
  unfold Tripod.relRamIdx
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ w.maximalIdeal.ne_bot,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ w.maximalIdeal.ne_bot]
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup w.maximalIdeal.asIdeal _ _ (K ≃ₐ[k] K)

private lemma relInertDeg_le {v : FinitePlace K} {w : FinitePlace k}
    (h : FinitePlace.LiesOver v w) : Tripod.relInertDeg v w ≤ inertDeg K v := by
  change Tripod.relInertDeg v w ≤ Tripod.inertDeg K v
  rw [Tripod.inertDeg_eq_mul h]
  exact Nat.le_mul_of_pos_left _ (Tripod.inertDeg_pos' w)

/-- Sum the local degree bounds over places representing the given residue characteristics. -/
private lemma finrank_mul_sum_log_le (s : Finset ℕ) (W : Finset (FinitePlace k))
    (a : FinitePlace K → ℕ) (hs : s ⊆ W.image residueChar)
    (ha : ∀ w ∈ W, ∀ v ∈ placesOver K w, Tripod.relLocalDeg v w ≤ 2 * (a v * inertDeg K v)) :
    (Module.finrank k K : ℝ) * ∑ p ∈ s, Real.log p ≤
      2 * ∑ v ∈ W.biUnion (placesOver K),
        (a v : ℝ) * ((inertDeg K v : ℝ) * Real.log (residueChar v)) := by
  classical
  have hlog : ∑ p ∈ s, Real.log p ≤ ∑ w ∈ W, Real.log (residueChar w) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun p _ _ => Real.log_natCast_nonneg p)).trans ?_
    exact Finset.sum_image_le_of_nonneg fun p _ => Real.log_natCast_nonneg p
  have hlocal (w : FinitePlace k) (hw : w ∈ W) :
      (Module.finrank k K : ℝ) * Real.log (residueChar w) ≤
        2 * ∑ v ∈ placesOver K w,
          (a v : ℝ) * ((inertDeg K v : ℝ) * Real.log (residueChar v)) := by
    have hdegree : Module.finrank k K ≤ 2 * ∑ v ∈ placesOver K w, a v * inertDeg K v := by
      have hsum : ∑ v ∈ placesOver K w, Tripod.relLocalDeg v w = Module.finrank k K :=
        sum_placesOver_mul_eq_finrank w
      rw [← hsum, Finset.mul_sum]
      exact Finset.sum_le_sum fun v hv => ha w hw v hv
    calc
      _ ≤ ((2 * ∑ v ∈ placesOver K w, a v * inertDeg K v : ℕ) : ℝ) *
            Real.log (residueChar w) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) (Real.log_natCast_nonneg _)
      _ = _ := by
        push_cast
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun v hv => ?_
        have hvw : FinitePlace.LiesOver v w := mem_placesOver.mp hv
        have hp : residueChar v = residueChar w :=
          Tripod.residueChar_eq_of_liesOver hvw
        rw [hp, mul_assoc]
  calc
    _ ≤ (Module.finrank k K : ℝ) * ∑ w ∈ W, Real.log (residueChar w) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = ∑ w ∈ W, (Module.finrank k K : ℝ) * Real.log (residueChar w) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ w ∈ W, 2 * ∑ v ∈ placesOver K w,
        (a v : ℝ) * ((inertDeg K v : ℝ) * Real.log (residueChar v)) :=
      Finset.sum_le_sum hlocal
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_biUnion (placesOver_pairwiseDisjoint W)]

end FinitePlaces

section DifferentLower

attribute [local instance] FractionRing.liftAlgebra

variable {T : Type*} [Field T] [NumberField T]

/-- The absolute different has exponent at least e_v − 1 at each finite place. -/
private lemma ramIdx_sub_one_le_multiplicity_different (v : FinitePlace T) :
    ramIdx T v - 1 ≤ multiplicity v.maximalIdeal.asIdeal (differentIdeal ℤ (𝓞 T)) := by
  let p := v.maximalIdeal.asIdeal.under ℤ
  haveI : p.IsMaximal := Tripod.under_int_isMaximal v
  have hp : p ≠ ⊥ := Tripod.under_int_ne_bot v
  haveI : v.maximalIdeal.asIdeal.LiesOver p := inferInstance
  have he : ramIdx T v = p.ramificationIdx' v.maximalIdeal.asIdeal :=
    (Ideal.ramificationIdx'_eq_ramificationIdx p v.maximalIdeal.asIdeal hp).symm
  have hdvd : v.maximalIdeal.asIdeal ^ ramIdx T v ∣ p.map (algebraMap ℤ (𝓞 T)) := by
    rw [he, Ideal.dvd_iff_le]
    exact Ideal.le_pow_ramificationIdx'
  have hmult : FiniteMultiplicity v.maximalIdeal.asIdeal (differentIdeal ℤ (𝓞 T)) :=
    FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_isPrime v.maximalIdeal.ne_bot v.maximalIdeal.isPrime) differentIdeal_ne_bot
  exact hmult.pow_dvd_iff_le_multiplicity.mp
    (pow_sub_one_dvd_differentIdeal ℤ (p := p) v.maximalIdeal.asIdeal (ramIdx T v) hp hdvd)

/-- A sum of the lower bounds is bounded by the logarithmic norm of the absolute different. -/
private lemma sum_ramIdx_sub_one_log_le (s : Finset (FinitePlace T)) :
    ∑ v ∈ s, ((ramIdx T v - 1 : ℕ) : ℝ) *
        ((inertDeg T v : ℝ) * Real.log (residueChar v)) ≤
      Module.finrank ℚ T * logDifferentDeg T := by
  classical
  let I := differentIdeal ℤ (𝓞 T)
  have hI : I ≠ ⊥ := differentIdeal_ne_bot
  let S := s.image (fun v => v.maximalIdeal) ∪ primeSupport hI
  have hT : (0 : ℝ) < Module.finrank ℚ T := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ T)
  rw [logDifferentDeg, mul_div_cancel₀ _ hT.ne']
  change _ ≤ Real.log (Ideal.absNorm I)
  rw [log_absNorm_eq_finsum hI, finsum_eq_sum_of_support_subset (s := S)]
  · calc
      _ ≤ ∑ v ∈ s, (multiplicity v.maximalIdeal.asIdeal I : ℝ) *
          Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [Tripod.absNorm_eq_pow_residueChar, Nat.cast_pow, Real.log_pow]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast ramIdx_sub_one_le_multiplicity_different v)
          (mul_nonneg (by positivity) (Real.log_natCast_nonneg _))
      _ = ∑ P ∈ s.image (fun v => v.maximalIdeal),
          (multiplicity P.asIdeal I : ℝ) * Real.log (Ideal.absNorm P.asIdeal) := by
        rw [Finset.sum_image]
        intro v _ v' _ h
        exact FinitePlace.maximalIdeal_injective h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun P _ _ => mul_nonneg (by positivity) (Real.log_natCast_nonneg _))
  · intro P hP
    change P ∈ S
    by_contra h
    have hdiv : ¬ P.asIdeal ∣ I := fun hdiv =>
      h (Finset.mem_union_right _ ((mem_primeSupport hI P).mpr hdiv))
    apply hP
    change (multiplicity P.asIdeal I : ℝ) * Real.log (Ideal.absNorm P.asIdeal) = 0
    rw [multiplicity_eq_zero.mpr hdiv, Nat.cast_zero, zero_mul]

end DifferentLower

section Tripodal

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

private lemma isBadTpdOf_of_liesOver {v : FinitePlace ↥(tripodalFieldOf F E)}
    {w : FinitePlace ↥(fieldOfModuli F E)} (hw : w ∈ VBad) (hvw : FinitePlace.LiesOver v w) :
    IsBadTpdOf F E VBad v := by
  obtain ⟨z, hzv⟩ := FinitePlace.exists_liesOver (K := F) v
  haveI : z.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hzv
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  exact ⟨z, ⟨w, hw, Ideal.LiesOver.trans z.maximalIdeal.asIdeal v.maximalIdeal.asIdeal
    w.maximalIdeal.asIdeal⟩, hzv⟩

private lemma exists_vbad_of_isBadTpdOf {v : FinitePlace ↥(tripodalFieldOf F E)}
    (hv : IsBadTpdOf F E VBad v) : ∃ w ∈ VBad, residueChar w = residueChar v := by
  obtain ⟨z, ⟨w, hw, hzw⟩, hzv⟩ := hv
  exact ⟨w, hw, (Tripod.residueChar_eq_of_liesOver hzw).symm.trans
    (Tripod.residueChar_eq_of_liesOver hzv)⟩

/-- Bound the logarithmic sum for residue characteristics of bad places by the conductor. -/
lemma sum_bad_log_le (he2 : RelRamIdxModLeTwo E VBad)
    (hfin : (badPlacesOver F E VBad).Finite)
    (B : Finset ℕ) (hB : ∀ p ∈ B, ∃ w ∈ VBad, residueChar w = p) :
    (Module.finrank ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) : ℝ) *
        ∑ p ∈ B, Real.log p ≤
      2 * Module.finrank ℚ ↥(tripodalFieldOf F E) * logConductorDegOf F E VBad := by
  classical
  let T := ↥(tripodalFieldOf F E)
  choose w hwBad hwChar using hB
  let W := B.attach.image (fun p => w p.1 p.2)
  let U := W.biUnion (placesOver T)
  have hsub : B ⊆ W.image residueChar := by
    intro p hp
    exact Finset.mem_image.mpr ⟨w p hp,
      Finset.mem_image_of_mem _ (Finset.mem_attach B ⟨p, hp⟩), hwChar p hp⟩
  have hW (w₀ : FinitePlace ↥(fieldOfModuli F E)) (hw₀ : w₀ ∈ W) : w₀ ∈ VBad := by
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw₀
    exact hwBad p.1 p.2
  have hdegree (w₀ : FinitePlace ↥(fieldOfModuli F E)) (hw₀ : w₀ ∈ W)
      (v : FinitePlace T) (hv : v ∈ placesOver T w₀) :
      Tripod.relLocalDeg v w₀ ≤ 2 * (1 * inertDeg T v) := by
    have hvw : FinitePlace.LiesOver v w₀ := mem_placesOver.mp hv
    rw [one_mul]
    exact Nat.mul_le_mul (he2 v w₀ (hW w₀ hw₀) hvw) (relInertDeg_le hvw)
  have hsum := finrank_mul_sum_log_le B W (fun (_ : FinitePlace T) => 1) hsub hdegree
  have hcond := sum_bad_inertDeg_div_le hfin U (fun v hv => by
    obtain ⟨w₀, hw₀, hvw⟩ := Finset.mem_biUnion.mp hv
    exact isBadTpdOf_of_liesOver (hW w₀ hw₀) (mem_placesOver.mp hvw))
  have hT : (0 : ℝ) < Module.finrank ℚ T := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ T)
  rw [← Finset.sum_div, div_le_iff₀ hT] at hcond
  calc
    _ ≤ 2 * ∑ v ∈ U, (inertDeg T v : ℝ) * Real.log (residueChar v) := by
      simpa only [Nat.cast_one, one_mul] using hsum
    _ ≤ 2 * (logConductorDegOf F E VBad * Module.finrank ℚ T) :=
      mul_le_mul_of_nonneg_left hcond (by norm_num)
    _ = _ := by ring

private lemma subset_image_of_attached_representatives {α : Type*} {β : Type*}
    [DecidableEq α] [DecidableEq β]
    (R : Finset α) (f : R → β) (r : β → α) (hr : ∀ p : R, r (f p) = p.1) :
    R ⊆ (R.attach.image f).image r := by
  intro p hp
  let x : R := ⟨p, hp⟩
  exact Finset.mem_image.mpr ⟨f x, Finset.mem_image_of_mem f (Finset.mem_attach R x), hr x⟩

/-- Bound the logarithmic sum for residue characteristics ramified in the tripodal field. -/
lemma sum_ramified_log_le [IsGalois ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E)]
    (R : Finset ℕ) (hR : ∀ p ∈ R, ∃ v : FinitePlace ↥(tripodalFieldOf F E),
      residueChar v = p ∧ ramIdx ↥(tripodalFieldOf F E) v ≠ 1) :
    (Module.finrank ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) : ℝ) *
        ∑ p ∈ R, Real.log p ≤
      2 * Module.finrank ℚ ↥(tripodalFieldOf F E) * logDifferentDeg ↥(tripodalFieldOf F E) := by
  classical
  let T := ↥(tripodalFieldOf F E)
  let M := ↥(fieldOfModuli F E)
  choose v hvChar hvRam using hR
  let W := R.attach.image (fun p => Tripod.placeUnder (k := M) (v p.1 p.2))
  let U := W.biUnion (placesOver T)
  have hplace (p : R) : residueChar (Tripod.placeUnder (k := M) (v p.1 p.2)) = p.1 := by
    have hchar : residueChar (v p.1 p.2) =
        residueChar (Tripod.placeUnder (k := M) (v p.1 p.2)) :=
      Tripod.residueChar_eq_of_liesOver (Tripod.liesOver_placeUnder (k := M) (v p.1 p.2))
    exact hchar.symm.trans (hvChar p.1 p.2)
  have hsub : R ⊆ W.image residueChar :=
    subset_image_of_attached_representatives R _ residueChar hplace
  have hdegree (w₀ : FinitePlace M) (hw₀ : w₀ ∈ W)
      (v' : FinitePlace T) (hv' : v' ∈ placesOver T w₀) :
      Tripod.relLocalDeg v' w₀ ≤ 2 * ((ramIdx T v' - 1) * inertDeg T v') := by
    have hv'w : FinitePlace.LiesOver v' w₀ := mem_placesOver.mp hv'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw₀
    have hvw := Tripod.liesOver_placeUnder (k := M) (v p.1 p.2)
    have he : ramIdx T v' = ramIdx T (v p.1 p.2) := by
      change Tripod.ramIdx T v' = Tripod.ramIdx T (v p.1 p.2)
      rw [Tripod.ramIdx_eq_mul hv'w, Tripod.ramIdx_eq_mul hvw, relRamIdx_eq_of_isGalois hv'w hvw]
    have he2 : 2 ≤ ramIdx T v' := by
      rw [he]
      have hpos := Tripod.ramIdx_pos' (v p.1 p.2)
      have hne := hvRam p.1 p.2
      change 0 < ramIdx T (v p.1 p.2) at hpos
      change ramIdx T (v p.1 p.2) ≠ 1 at hne
      omega
    have hrel : Tripod.relRamIdx v' (Tripod.placeUnder (k := M) (v p.1 p.2)) ≤ ramIdx T v' := by
      change _ ≤ Tripod.ramIdx T v'
      rw [Tripod.ramIdx_eq_mul hv'w]
      exact Nat.le_mul_of_pos_left _ (Tripod.ramIdx_pos' _)
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul (by omega) (relInertDeg_le hv'w)
  calc
    _ ≤ 2 * ∑ v ∈ U, ((ramIdx T v - 1 : ℕ) : ℝ) *
        ((inertDeg T v : ℝ) * Real.log (residueChar v)) :=
      finrank_mul_sum_log_le R W (fun v => ramIdx T v - 1) hsub hdegree
    _ ≤ 2 * (Module.finrank ℚ T * logDifferentDeg T) :=
      mul_le_mul_of_nonneg_left (sum_ramIdx_sub_one_log_le U) (by norm_num)
    _ = _ := by ring

end Tripodal

section Distinguished

private lemma sum_log_insert_le (p : ℕ) (s : Finset ℕ) :
    ∑ q ∈ insert p s, Real.log q ≤ Real.log p + ∑ q ∈ s, Real.log q := by
  by_cases hp : p ∈ s
  · rw [Finset.insert_eq_of_mem hp]
    exact le_add_of_nonneg_left (Real.log_natCast_nonneg p)
  · rw [Finset.sum_insert hp]

private lemma log_two_add_log_three_add_log_five_le :
    Real.log 2 + Real.log 3 + Real.log 5 ≤ 5 := by
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (2 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by rw [Real.log_pow, Nat.cast_ofNat]
  have h5 : Real.log 5 ≤ 3 * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (3 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by rw [Real.log_pow, Nat.cast_ofNat]
  linarith [Real.log_two_lt_d9]

private lemma sum_log_small_le (ℓ : ℕ) :
    ∑ p ∈ ({2, 3, 5, ℓ} : Finset ℕ), Real.log p ≤ 5 + Real.log ℓ := by
  have h2 := sum_log_insert_le 2 {3, 5, ℓ}
  have h3 := sum_log_insert_le 3 {5, ℓ}
  have h5 := sum_log_insert_le 5 {ℓ}
  simp only [Finset.sum_singleton, Nat.cast_ofNat] at h2 h3 h5
  linarith [log_two_add_log_three_add_log_five_le]

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-- Step (iii) of IUT IV, Theorem 1.10, for distinguished primes of the same torsion tower. -/
theorem sum_log_distinguished_le (H : TowerLocalFacts E VBad Pr) (he2 : RelRamIdxModLeTwo E VBad)
    [IsGalois ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E)]
    (hfin : (badPlacesOver F E VBad).Finite) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ ({2, 3, 5, Pr.ℓ} : Finset ℕ) ∨
      (∃ w ∈ badPlacesOver F E VBad, residueChar w = p) ∨
      (∃ v : FinitePlace ↥Pr.torsionField, residueChar v = p ∧ ramIdx (↥Pr.torsionField) v ≠ 1)) :
    ∑ p ∈ S, Real.log p ≤
      2 * Module.finrank ℚ ↥(fieldOfModuli F E) *
        (logDifferentDeg ↥(tripodalFieldOf F E) + logConductorDegOf F E VBad) + 5 +
          Real.log Pr.ℓ := by
  classical
  let T := ↥(tripodalFieldOf F E)
  let M := ↥(fieldOfModuli F E)
  let n : ℝ := Module.finrank M T
  let d : ℝ := Module.finrank ℚ M
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank M T)
  have hdegree : (Module.finrank ℚ T : ℝ) = d * n := by
    dsimp [d, n]
    exact_mod_cast finrank_tripodal_eq_mul F E
  let P : Finset ℕ := {2, 3, 5, Pr.ℓ}
  let S' := S.filter (fun p => p ∉ P)
  let B := S'.filter (fun p => ∃ w ∈ VBad, residueChar w = p)
  let R := S'.filter (fun p => ¬ ∃ w ∈ VBad, residueChar w = p)
  have hsmall : ∑ p ∈ S.filter (fun p => p ∈ P), Real.log p ≤ 5 + Real.log Pr.ℓ :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun _ hp => (Finset.mem_filter.mp hp).2)
      (fun p _ _ => Real.log_natCast_nonneg p)).trans (sum_log_small_le Pr.ℓ)
  have hB : ∀ p ∈ B, ∃ w ∈ VBad, residueChar w = p :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hR : ∀ p ∈ R, ∃ v : FinitePlace T, residueChar v = p ∧ ramIdx T v ≠ 1 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpS := Finset.mem_filter.mp hp'.1
    have hnot := hp'.2
    rcases hS p hpS.1 with h | ⟨w, ⟨w₀, hw₀, hww₀⟩, hwp⟩ | ⟨v, hvp, hv⟩
    · exact (hpS.2 h).elim
    · exact (hnot ⟨w₀, hw₀, (Tripod.residueChar_eq_of_liesOver hww₀).symm.trans hwp⟩).elim
    · refine ⟨placeTpd F E Pr.torsionField v, (residueChar_placeTpd v).trans hvp, ?_⟩
      have hgood : ¬ IsBadTpdOf F E VBad (placeTpd F E Pr.torsionField v) := by
        intro hbad
        obtain ⟨w₀, hw₀, hw₀v⟩ := exists_vbad_of_isBadTpdOf hbad
        exact hnot ⟨w₀, hw₀, hw₀v.trans ((residueChar_placeTpd v).trans hvp)⟩
      have hpv : residueChar v ∉ P := by
        rw [hvp]
        exact hpS.2
      have he := H.relRamIdx_eq_one v hpv hgood
      rw [ramIdx_eq_ramIdx_placeTpd_mul (F := F) (E := E) v, he, mul_one] at hv
      exact hv
  have hsum : ∑ p ∈ S', Real.log p ≤ 2 * d *
      (logDifferentDeg T + logConductorDegOf F E VBad) := by
    have hsplit : (∑ p ∈ B, Real.log p) + (∑ p ∈ R, Real.log p) = ∑ p ∈ S', Real.log p :=
      Finset.sum_filter_add_sum_filter_not S' (fun p => ∃ w ∈ VBad, residueChar w = p) _
    apply le_of_mul_le_mul_left ?_ hn
    rw [← hsplit, mul_add]
    calc
      _ ≤ (2 * Module.finrank ℚ T * logConductorDegOf F E VBad) +
          (2 * Module.finrank ℚ T * logDifferentDeg T) :=
        add_le_add (sum_bad_log_le he2 hfin B hB) (sum_ramified_log_le (F := F) (E := E) R hR)
      _ = _ := by
        rw [hdegree]
        ring
  calc
    _ = (∑ p ∈ S.filter (fun p => p ∈ P), Real.log p) + ∑ p ∈ S', Real.log p :=
      (Finset.sum_filter_add_sum_filter_not S (fun p => p ∈ P) _).symm
    _ ≤ (5 + Real.log Pr.ℓ) + 2 * d * (logDifferentDeg T + logConductorDegOf F E VBad) :=
      add_le_add hsmall hsum
    _ = 2 * d * (logDifferentDeg T + logConductorDegOf F E VBad) + 5 + Real.log Pr.ℓ := by
      ring

end Distinguished

end AbcAdaptation.Reference.Iut
