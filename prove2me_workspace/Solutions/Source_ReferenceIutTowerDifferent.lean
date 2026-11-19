/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/Different.lean
-/
import Solutions.Source_ReferenceIutTowerDifferentFormula
import Solutions.Source_ReferenceIutTowerDifferentArithmetic
import Solutions.Source_ReferenceIutTowerDifferentBound
import Solutions.Source_FermatBelyiDifferentAccounting

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain
open scoped BigOperators Classical

universe u

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

variable (Pr)

/-- **The bound on the different of `K/F_tpd`** from the local facts:
`log N(𝔇_{K/F_tpd})/[K : ℚ] ≤ log(f_{F_tpd}) + ∑_{p ∈ {2,3,5,ℓ}} (1 + c_p)·log p`. -/
theorem log_absNorm_different_div_le (H : TowerLocalFacts E VBad Pr)
    (hfin : (badPlacesOver F E VBad).Finite) :
    Real.log (Ideal.absNorm
        (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField))) /
        Module.finrank ℚ ↥Pr.torsionField ≤
      logConductorDegOf F E VBad +
        ∑ p ∈ ({2, 3, 5, Pr.ℓ} : Finset ℕ), (1 + wildConst Pr.ℓ p) * Real.log p := by
  classical
  -- the termwise bound `ord_v(𝔇) ≤ (e(v/u) − 1) + e_v c_p`
  have hord : ∀ v : FinitePlace ↥Pr.torsionField,
      (ordAt (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) v : ℝ) ≤
      ((Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) +
        ramIdx (↥Pr.torsionField) v * wildConst Pr.ℓ (residueChar v) := by
    intro v
    have h1 := H.ordAt_different_le v
    have h2 := Nat.pos_of_ne_zero (Tripod.relRamIdx_ne_zero (liesOver_placeTpd (F := F) (E := E) v))
    have h3 : ordAt (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) v ≤
        (Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) - 1) +
        ramIdx (↥Pr.torsionField) v * wildConst Pr.ℓ (residueChar v) := by omega
    exact_mod_cast h3
  set T := ↥(tripodalFieldOf F E)
  set K := ↥Pr.torsionField
  set 𝔇 := differentIdeal (𝓞 T) (𝓞 K)
  set P : Finset ℕ := {2, 3, 5, Pr.ℓ}
  have h𝔇 : 𝔇 ≠ ⊥ := differentIdeal_ne_bot
  let primes := Tripod.Fermat.Proper.ConductorExtensionSource.primeSupport h𝔇
  let s := primes.map (FinitePlace.equivHeightOneSpectrum (K := K)).symm.toEmbedding
  have hnorm : Real.log (Ideal.absNorm 𝔇) =
      ∑ v ∈ s, (ordAt 𝔇 v : ℝ) * (inertDeg K v * Real.log (residueChar v)) := by
    rw [Tripod.Fermat.Proper.ConductorExtensionSource.log_absNorm_eq_finsum h𝔇,
      finsum_eq_sum_of_support_subset (s := primes)]
    · dsimp only [s]
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun P _ => ?_
      let v := FinitePlace.mk P
      change (multiplicity P.asIdeal 𝔇 : ℝ) * Real.log (Ideal.absNorm P.asIdeal) =
        (ordAt 𝔇 v : ℝ) * (inertDeg K v * Real.log (residueChar v))
      have hv : v.maximalIdeal = P := FinitePlace.maximalIdeal_mk P
      rw [ordAt_eq_multiplicity 𝔇 h𝔇 v, ← hv, Tripod.absNorm_eq_pow_residueChar,
        Nat.cast_pow, Real.log_pow] <;> rfl
    · intro P hP
      rw [Finset.mem_coe, Tripod.Fermat.Proper.ConductorExtensionSource.mem_primeSupport]
      by_contra h
      rw [Function.mem_support] at hP
      exact hP (by simp [multiplicity_eq_zero.mpr h])
  have hK0 : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hlog : ∀ p : ℕ, 0 ≤ Real.log p := fun p => Real.log_natCast_nonneg p
  rw [hnorm, Finset.sum_div]
  -- split into the tame and the wild part
  have hsplit : ∑ v ∈ s, (ordAt 𝔇 v : ℝ) * (inertDeg K v * Real.log (residueChar v)) /
      Module.finrank ℚ K ≤
      ∑ v ∈ s, ((Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
        (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K +
      ∑ v ∈ s, placeWeight K v * (wildConst Pr.ℓ (residueChar v) * Real.log (residueChar v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have hfl : 0 ≤ (inertDeg K v : ℝ) * Real.log (residueChar v) := by
      exact mul_nonneg (by positivity) (hlog _)
    have hw : placeWeight K v * (wildConst Pr.ℓ (residueChar v) * Real.log (residueChar v)) =
        (ramIdx K v * wildConst Pr.ℓ (residueChar v) : ℝ) *
          (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K := by
      unfold placeWeight localDeg
      push_cast
      ring
    rw [hw, ← add_div, ← add_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hord v) hfl) hK0.le
  refine hsplit.trans ?_
  -- the wild part
  have hwild := sum_placeWeight_wildConst_le (K := K) Pr.ℓ s
  -- the tame part: only the places ramified in `K/F_tpd` contribute
  set s' := s.filter (fun v => Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) ≠ 1) with hs'
  have htame1 : ∑ v ∈ s, ((Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
      (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K =
      ∑ v ∈ s', ((Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
      (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · rfl
    · rw [not_not] at h
      rw [h]
      simp
  -- group by the place of `F_tpd` below
  set t := s'.image (placeTpd F E Pr.torsionField) with ht
  have htame2 : ∑ v ∈ s', ((Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
      (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K ≤
      ∑ u ∈ t, (inertDeg T u : ℝ) * Real.log (residueChar u) / Module.finrank ℚ T := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := t) (g := placeTpd F E Pr.torsionField)
      (fun v hv => Finset.mem_image_of_mem _ hv)]
    exact Finset.sum_le_sum fun u _ => sum_tame_fiber_le Pr s' u
  -- the places of `t` have residue characteristic in `P` or are bad
  have htP : ∀ u ∈ t, residueChar u ∉ P → IsBadTpdOf F E VBad u := by
    intro u hu hp
    rw [ht, Finset.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [hs', Finset.mem_filter] at hv
    by_contra hbad
    rw [residueChar_placeTpd] at hp
    exact hv.2 (H.relRamIdx_eq_one v hp hbad)
  have htame3 : ∑ u ∈ t, (inertDeg T u : ℝ) * Real.log (residueChar u) / Module.finrank ℚ T ≤
      ∑ p ∈ P, Real.log p + logConductorDegOf F E VBad := by
    rw [← Finset.sum_filter_add_sum_filter_not t (fun u => residueChar u ∈ P)]
    refine add_le_add ?_ ?_
    · rw [← Finset.sum_fiberwise_of_maps_to (s := t.filter (fun u => residueChar u ∈ P)) (t := P)
        (g := residueChar) (fun u hu => (Finset.mem_filter.mp hu).2)]
      refine Finset.sum_le_sum fun p _ => ?_
      calc ∑ u ∈ (t.filter (fun u => residueChar u ∈ P)).filter (fun u => residueChar u = p),
            (inertDeg T u : ℝ) * Real.log (residueChar u) / Module.finrank ℚ T
          = (∑ u ∈ (t.filter (fun u => residueChar u ∈ P)).filter (fun u => residueChar u = p),
              (inertDeg T u : ℝ) / Module.finrank ℚ T) * Real.log p := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [(Finset.mem_filter.mp hu).2]
            ring
        _ ≤ 1 * Real.log p :=
            mul_le_mul_of_nonneg_right (sum_inertDeg_div_filter_le _ p) (hlog p)
        _ = Real.log p := one_mul _
    · exact sum_bad_inertDeg_div_le hfin _ fun u hu =>
        htP u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  have hfinal : ∑ p ∈ P, Real.log p + ∑ p ∈ P, wildConst Pr.ℓ p * Real.log p =
      ∑ p ∈ P, (1 + wildConst Pr.ℓ p) * Real.log p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [htame1]
  linarith only [htame2, htame3, hwild, hfinal]

/-- **Step (ii)**: `log(d_K) ≤ log(d_{F_tpd}) + log(f_{F_tpd}) + 2·log ℓ + 21`. -/
theorem logDifferentDeg_torsionField_le (H : TowerLocalFacts E VBad Pr)
    (hfin : (badPlacesOver F E VBad).Finite) :
    logDifferentDeg ↥Pr.torsionField ≤ logDifferentDeg ↥(tripodalFieldOf F E) +
      logConductorDegOf F E VBad + 2 * Real.log Pr.ℓ + 21 := by
  rw [logDifferentDeg_torsionField_eq]
  have h1 := log_absNorm_different_div_le Pr H hfin
  have h2 := sum_one_add_wildConst_le Pr.ℓ Pr.five_le
  have h3 := constant_le_21
  linarith only [h1, h2, h3]

end AbcAdaptation.Reference.Iut
