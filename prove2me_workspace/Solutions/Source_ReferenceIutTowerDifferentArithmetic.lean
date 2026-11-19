/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/Different.lean
-/
import Solutions.Source_ReferenceIutTowerLocalFacts
import Solutions.Source_TripodFinitePrimeCounting
import Solutions.Source_FermatConductorPlaceDegree
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain
open scoped BigOperators Classical

universe u

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-- The weights of any finite set of places of residue characteristic `p` sum to at most one. -/
lemma sum_placeWeight_filter_le {K : Type*} [Field K] [NumberField K]
    (s : Finset (FinitePlace K)) (p : ℕ) :
    ∑ v ∈ s.filter (fun v => residueChar v = p), placeWeight K v ≤ 1 := by
  unfold placeWeight
  rw [← Finset.sum_div, div_le_one (by exact_mod_cast (Module.finrank_pos :
    0 < Module.finrank ℚ K))]
  change (∑ v ∈ s.filter (fun v => residueChar v = p), (Tripod.localDeg K v : ℝ)) ≤ _
  exact_mod_cast Tripod.sum_localDeg_filter_le s p

/-- The normalized inertia degrees over a rational prime sum to at most one. -/
lemma sum_inertDeg_div_filter_le {T : Type*} [Field T] [NumberField T]
    (s : Finset (FinitePlace T)) (p : ℕ) :
    ∑ w ∈ s.filter (fun w => residueChar w = p), (inertDeg T w : ℝ) / Module.finrank ℚ T ≤ 1 := by
  rw [← Finset.sum_div, div_le_one (by exact_mod_cast (Module.finrank_pos :
    0 < Module.finrank ℚ T))]
  change (∑ w ∈ s.filter (fun w => residueChar w = p), (Tripod.inertDeg T w : ℝ)) ≤ _
  exact_mod_cast Tripod.sum_inertDeg_filter_le s p

/-- Bound the wild contribution by grouping the finite places by residue characteristic. -/
lemma sum_placeWeight_wildConst_le {K : Type*} [Field K] [NumberField K] (ℓ : ℕ)
    (s : Finset (FinitePlace K)) :
    ∑ v ∈ s, placeWeight K v * (wildConst ℓ (residueChar v) * Real.log (residueChar v)) ≤
      ∑ p ∈ ({2, 3, 5, ℓ} : Finset ℕ), wildConst ℓ p * Real.log p := by
  set P : Finset ℕ := {2, 3, 5, ℓ}
  have h1 : ∑ v ∈ s, placeWeight K v * (wildConst ℓ (residueChar v) * Real.log (residueChar v)) =
      ∑ v ∈ s.filter (fun v => residueChar v ∈ P),
        placeWeight K v * (wildConst ℓ (residueChar v) * Real.log (residueChar v)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · rfl
    · rw [wildConst_eq_zero h]
      simp
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := s.filter (fun v => residueChar v ∈ P)) (t := P)
    (g := residueChar) (fun v hv => (Finset.mem_filter.mp hv).2)]
  refine Finset.sum_le_sum fun p _ => ?_
  calc ∑ v ∈ (s.filter (fun v => residueChar v ∈ P)).filter (fun v => residueChar v = p),
        placeWeight K v * (wildConst ℓ (residueChar v) * Real.log (residueChar v))
      = (∑ v ∈ (s.filter (fun v => residueChar v ∈ P)).filter (fun v => residueChar v = p),
          placeWeight K v) * (wildConst ℓ p * Real.log p) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2]
    _ ≤ 1 * (wildConst ℓ p * Real.log p) :=
      mul_le_mul_of_nonneg_right (sum_placeWeight_filter_le _ p)
        (mul_nonneg (by positivity) (Real.log_natCast_nonneg p))
    _ = wildConst ℓ p * Real.log p := one_mul _

variable (Pr) in
/-- Bound the tame contribution of places of the torsion field over a single place of `F_tpd`. -/
lemma sum_tame_fiber_le (s : Finset (FinitePlace ↥Pr.torsionField))
    (w : FinitePlace ↥(tripodalFieldOf F E)) :
    ∑ v ∈ s.filter (fun v => placeTpd F E Pr.torsionField v = w),
      ((Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
        (inertDeg (↥Pr.torsionField) v * Real.log (residueChar v)) /
          Module.finrank ℚ ↥Pr.torsionField ≤
      (inertDeg ↥(tripodalFieldOf F E) w : ℝ) * Real.log (residueChar w) /
        Module.finrank ℚ ↥(tripodalFieldOf F E) := by
  set T := ↥(tripodalFieldOf F E)
  set K := ↥Pr.torsionField
  letI : FiniteDimensional T K := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hKT : Module.finrank ℚ K = Module.finrank ℚ T * Module.finrank T K :=
    (Module.finrank_mul_finrank ℚ T K).symm
  have hTK0 : (0 : ℝ) < Module.finrank T K := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank T K)
  have hlog : 0 ≤ Real.log (residueChar w) := Real.log_natCast_nonneg _
  have hterm : ∀ v ∈ s.filter (fun v => placeTpd F E Pr.torsionField v = w),
      ((Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
        (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K ≤
      ((Tripod.relRamIdx v w * Tripod.relInertDeg v w : ℕ) : ℝ) *
        (inertDeg T w * Real.log (residueChar w)) / Module.finrank ℚ K := by
    intro v hv
    have hvw : placeTpd F E Pr.torsionField v = w := (Finset.mem_filter.mp hv).2
    have hrc : residueChar v = residueChar w := by rw [← hvw, residueChar_placeTpd]
    have hf : inertDeg K v = inertDeg T w * Tripod.relInertDeg v w := by
      rw [← hvw]
      exact inertDeg_eq_inertDeg_placeTpd_mul v
    rw [hvw, hrc, hf]
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast only [Nat.cast_mul]
    have h1 : ((Tripod.relRamIdx v w - 1 : ℕ) : ℝ) ≤ Tripod.relRamIdx v w := by
      exact_mod_cast Nat.sub_le _ _
    calc ((Tripod.relRamIdx v w - 1 : ℕ) : ℝ) *
          (inertDeg T w * Tripod.relInertDeg v w * Real.log (residueChar w))
        ≤ (Tripod.relRamIdx v w : ℝ) * (inertDeg T w * Tripod.relInertDeg v w *
            Real.log (residueChar w)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (Tripod.relRamIdx v w : ℝ) * Tripod.relInertDeg v w *
          (inertDeg T w * Real.log (residueChar w)) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_div, ← Finset.sum_mul]
  let over := Tripod.Fermat.Proper.ConductorExtensionSource.placesOver K w
  have hsub : s.filter (fun v => placeTpd F E Pr.torsionField v = w) ⊆ over := by
    intro v hv
    have hvw := (Finset.mem_filter.mp hv).2
    apply Tripod.Fermat.Proper.ConductorExtensionSource.mem_placesOver.mpr
    rw [← hvw]
    exact liesOver_placeTpd v
  have hsum : ∑ v ∈ over, Tripod.relRamIdx v w * Tripod.relInertDeg v w = Module.finrank T K :=
    Tripod.Fermat.Proper.ConductorExtensionSource.sum_placesOver_mul_eq_finrank w
  have hle : ∑ v ∈ s.filter (fun v => placeTpd F E Pr.torsionField v = w),
      ((Tripod.relRamIdx v w * Tripod.relInertDeg v w : ℕ) : ℝ) ≤ Module.finrank T K := by
    rw [← hsum, Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  calc (∑ v ∈ s.filter (fun v => placeTpd F E Pr.torsionField v = w),
        ((Tripod.relRamIdx v w * Tripod.relInertDeg v w : ℕ) : ℝ)) *
        (inertDeg T w * Real.log (residueChar w)) / Module.finrank ℚ K
      ≤ (Module.finrank T K : ℝ) * (inertDeg T w * Real.log (residueChar w)) /
          Module.finrank ℚ K := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (inertDeg T w : ℝ) * Real.log (residueChar w) / Module.finrank ℚ T := by
        rw [hKT, Nat.cast_mul, mul_comm ((Module.finrank ℚ T : ℕ) : ℝ),
          mul_div_mul_left _ _ hTK0.ne']

/-- Finitely many bad places of `F` give finitely many bad places of the tripodal field. -/
lemma isBadTpdOf_finite (hfin : (badPlacesOver F E VBad).Finite) :
    {w : FinitePlace ↥(tripodalFieldOf F E) | IsBadTpdOf F E VBad w}.Finite := by
  refine (hfin.image (Tripod.placeUnder (k := ↥(tripodalFieldOf F E)))).subset ?_
  rintro w ⟨v, hv, hvw⟩
  exact ⟨v, hv, Tripod.placeUnder_eq_of_liesOver_place hvw⟩

/-- The normalized contributions at a finite set of bad places are bounded by the conductor. -/
lemma sum_bad_inertDeg_div_le (hfin : (badPlacesOver F E VBad).Finite)
    (s : Finset (FinitePlace ↥(tripodalFieldOf F E))) (hs : ∀ w ∈ s, IsBadTpdOf F E VBad w) :
    ∑ w ∈ s, (inertDeg ↥(tripodalFieldOf F E) w : ℝ) * Real.log (residueChar w) /
      Module.finrank ℚ ↥(tripodalFieldOf F E) ≤ logConductorDegOf F E VBad := by
  unfold logConductorDegOf
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  let B := (isBadTpdOf_finite hfin).toFinset
  have hsB : s ⊆ B := fun w hw => (Set.Finite.mem_toFinset _).mpr (hs w hw)
  rw [finsum_eq_sum_of_support_subset (s := B)]
  · calc ∑ w ∈ s, (inertDeg ↥(tripodalFieldOf F E) w : ℝ) * Real.log (residueChar w)
        = ∑ w ∈ s, (if IsBadTpdOf F E VBad w then
            Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0) := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [if_pos (hs w hw), Tripod.absNorm_eq_pow_residueChar, Nat.cast_pow, Real.log_pow]
          rfl
      _ ≤ ∑ w ∈ B, (if IsBadTpdOf F E VBad w then
            Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsB fun w _ _ => ?_
          split_ifs
          · exact Real.log_natCast_nonneg _
          · exact le_rfl
  · intro w hw
    rw [Function.mem_support] at hw
    change w ∈ B
    apply (Set.Finite.mem_toFinset _).mpr
    by_contra h
    exact hw (if_neg h)

end AbcAdaptation.Reference.Iut
