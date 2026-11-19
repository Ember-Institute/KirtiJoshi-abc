/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/LogDK.lean
-/
import Solutions.Source_FermatBelyiDifferentAccounting
import Solutions.Source_ReferenceIutConcreteInvariants
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain
open scoped Classical BigOperators

universe u v

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] (LT : LocalTheory.{u, v} K)

private theorem ordDifferent_eq_multiplicity (K : Type u) [Field K] [NumberField K] (w : FinitePlace K) :
    ordDifferent K w = multiplicity w.maximalIdeal.asIdeal (differentIdeal ℤ (𝓞 K)) :=
  HeightOneSpectrum.count_normalizedFactors_eq_multiplicity differentIdeal_ne_bot w.maximalIdeal

private noncomputable def diffTerm (K : Type u) [Field K] [NumberField K] (w : FinitePlace K) : ℝ :=
  (ordDifferent K w : ℝ) * Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) / Module.finrank ℚ K

private theorem weighted_different_eq (K : Type u) [Field K] [NumberField K] (w : FinitePlace K) :
    placeWeight K w * differentExponent K w * Real.log (residueChar w) =
      diffTerm K w := by
  unfold diffTerm placeWeight differentExponent localDeg
  rw [Nat.cast_mul, Tripod.absNorm_eq_pow_residueChar, Nat.cast_pow, Real.log_pow]
  have he : (ramIdx K w : ℝ) ≠ 0 := by
    exact_mod_cast (Tripod.ramIdx_pos' w).ne'
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  have hf : inertDeg K w = Tripod.inertDeg K w := rfl
  have hp : residueChar w = Tripod.residueChar w := rfl
  rw [hf, hp]
  field_simp <;> ring

private theorem logDK_eq_sum_filter (p : ℕ) (s : Finset (FinitePlace K))
    (hs : ∀ w, ordDifferent K w ≠ 0 → w ∈ s) :
    LT.logDK p = ∑ w ∈ s.filter (fun w => residueChar w = p), diffTerm K w := by
  unfold logDK
  split_ifs with hp
  · letI : Finite {w : FinitePlace K // residueChar w = p} := LT.fiber_finite p
    letI : Fintype {w : FinitePlace K // residueChar w = p} := Fintype.ofFinite _
    trans ∑ w : {w : FinitePlace K // residueChar w = p}, diffTerm K w.1
    · refine Fintype.sum_equiv (LT.fiberFiniteEquiv ⟨p, hp⟩) _ _ ?_
      rintro ⟨w, hw⟩
      rcases w with w | w
      · have hpw := congrArg Subtype.val (RationalPlace.finite.inj hw)
        change residueChar w = p at hpw
        change placeWeight K w * differentExponent K w * Real.log (p : ℝ) = diffTerm K w
        rw [← hpw]
        exact weighted_different_eq K w
      · exact absurd hw (by simp [toRational])
    have hsum : ∑ w : {w : FinitePlace K // residueChar w = p}, diffTerm K w.1 =
        ∑ w ∈ (Finset.univ : Finset {w : FinitePlace K // residueChar w = p}).map
          (Function.Embedding.subtype _), diffTerm K w := by
      rw [Finset.sum_map] <;> rfl
    rw [hsum]
    symm
    refine Finset.sum_subset ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw
      exact Finset.mem_map.mpr ⟨⟨w, hw.2⟩, Finset.mem_univ _, rfl⟩
    · intro w hw hnot
      obtain ⟨⟨w', hw'⟩, _, rfl⟩ := Finset.mem_map.mp hw
      have hzero : ordDifferent K w' = 0 := by
        by_contra h
        exact hnot (Finset.mem_filter.mpr ⟨hs w' h, hw'⟩)
      simp [diffTerm, hzero]
  · symm
    refine Finset.sum_eq_zero fun w hw => ?_
    exact (hp ((Finset.mem_filter.mp hw).2 ▸ LT.residueChar_prime w)).elim

private theorem sum_diffTerm_eq (K : Type u) [Field K] [NumberField K]
    (s : Finset (FinitePlace K))
    (hs : ∀ w, ordDifferent K w ≠ 0 → w ∈ s) :
    ∑ w ∈ s, diffTerm K w = logDifferentDeg K := by
  have hI : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  rw [logDifferentDeg, Tripod.Fermat.Proper.ConductorExtensionSource.log_absNorm_eq_finsum hI,
    finsum_eq_sum_of_support_subset (s := s.map FinitePlace.equivHeightOneSpectrum.toEmbedding)]
  · rw [Finset.sum_map, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    change diffTerm K w = (multiplicity w.maximalIdeal.asIdeal (differentIdeal ℤ (𝓞 K)) : ℝ) *
      Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) / Module.finrank ℚ K
    rw [diffTerm, ordDifferent_eq_multiplicity]
  · intro P hP
    refine Finset.mem_map.mpr ⟨FinitePlace.mk P, hs _ ?_, FinitePlace.maximalIdeal_mk P⟩
    intro hzero
    rw [Function.mem_support] at hP
    apply hP
    have hmult : multiplicity P.asIdeal (differentIdeal ℤ (𝓞 K)) = 0 := by
      simpa only [ordDifferent_eq_multiplicity, FinitePlace.maximalIdeal_mk] using hzero
    simp [hmult]

/-- Summing the local contributions over any finite set containing the ramified
residue characteristics gives the normalized different degree of `K`. -/
theorem sum_logDK_eq (S : Finset ℕ) (hS : LT.ramifiedChars ⊆ S) :
    ∑ p ∈ S, LT.logDK p = logDifferentDeg K := by
  let s := LT.ramified_finite.toFinset
  have hs : ∀ w, ordDifferent K w ≠ 0 → w ∈ s := fun w hw =>
    LT.ramified_finite.mem_toFinset.mpr fun h => hw (LT.ordDifferent_eq_zero w h)
  have hmap : ∀ w ∈ s, residueChar w ∈ S := fun w hw =>
    hS (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  simp_rw [LT.logDK_eq_sum_filter _ s hs]
  rw [Finset.sum_fiberwise_of_maps_to (s := s) (t := S) (g := residueChar) hmap]
  exact sum_diffTerm_eq K s hs

end LocalTheory

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
  {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

/-- The distinguished primes exhaust the contributions to the different degree. -/
theorem ThetaLocalData.sum_dst_logDK_eq (TL : ThetaLocalData D LT) :
    ∑ p ∈ TL.dst, LT.logDK p = logDifferentDeg D.Kt :=
  LT.sum_logDK_eq TL.dst fun _ hp => Finset.mem_union_right _ hp

end AbcAdaptation.Reference.Iut
