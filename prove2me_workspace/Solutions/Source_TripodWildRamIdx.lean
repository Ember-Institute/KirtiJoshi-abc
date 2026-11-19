/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 2d8f000457da6447fa4df4bfec7365c1a49b6384
Original paths Iut/Tripod/WildRamIdx.lean and Iut/Tripod/TowerFacts.lean
-/
import Solutions.Source_ReferenceIutTowerWildBound
import Solutions.Source_TripodTpdDegree
import Solutions.Source_TripodTameTwo

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (R : (P.curve x).ModEllRepData ℓ)

/-- The torsion field is tamely ramified at places of residue characteristic away from `2, ℓ`. -/
theorem not_dvd_relRamIdx_torsionField_of_ne_two (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (v : FinitePlace ↥R.torsionField) (h2 : residueChar v ≠ 2) (hpℓ : residueChar v ≠ ℓ) :
    ¬ residueChar v ∣ relRamIdx v (placeUnder (k := (P.curve x).F) v) := by
  let u := placeTpd (P.curve x).F (P.curve x).E R.torsionField v
  have hvu : FinitePlace.LiesOver v u :=
    liesOver_placeTpd (F := (P.curve x).F) (E := (P.curve x).E) (L := R.torsionField) v
  have hvw := liesOver_placeUnder (k := (P.curve x).F) v
  have hwu := liesOver_placeUnder_of_liesOver (k := (P.curve x).F) hvu
  by_cases hu : u ∈ badT P x
  · letI : Fact (Nat.Prime (residueChar v)) := ⟨residueChar_prime v⟩
    letI : FiniteDimensional (P.curve x).F ↥R.torsionField :=
      Module.Finite.of_restrictScalars_finite ℚ _ _
    rw [relRamIdx_eq_card_inertia hvw]
    intro hdiv
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (residueChar v) hdiv
    apply hpℓ
    apply (Nat.prime_dvd_prime_iff_eq (residueChar_prime v) hℓ).mp
    rw [← hσ, orderOf_dvd_iff_pow_eq_one]
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      inertia_pow_eq_one_of_badT P x R hℓ hℓ2 v h2 hpℓ hu σ.1 σ.2
  · rw [relRamIdx_torsion_eq_one_at_good_place P x R hℓ hℓ2 hvw hwu h2 hpℓ hu]
    exact (residueChar_prime v).not_dvd_one

/-- The wild ramification bound of the Legendre tower. -/
theorem padicValNat_relRamIdx_le (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (v : FinitePlace ↥R.torsionField) :
    padicValNat (AbcAdaptation.Reference.Iut.residueChar v)
      (relRamIdx v (placeTpd (P.curve x).F (P.curve x).E R.torsionField v)) ≤
      wildConst ℓ (AbcAdaptation.Reference.Iut.residueChar v) := by
  letI : IsGalois (tpd P x) (P.curve x).F := isGalois_tpd_curve' (P := P) (x := x)
  let u := placeTpd (P.curve x).F (P.curve x).E R.torsionField v
  have hvu : FinitePlace.LiesOver v u :=
    liesOver_placeTpd (F := (P.curve x).F) (E := (P.curve x).E) (L := R.torsionField) v
  have hvw := liesOver_placeUnder (k := (P.curve x).F) v
  have hwu := liesOver_placeUnder_of_liesOver (k := (P.curve x).F) hvu
  have hℓ2 : ℓ ≠ 2 := by omega
  change padicValNat (residueChar v) (relRamIdx v u) ≤ wildConst ℓ (residueChar v)
  rw [relRamIdx_eq_mul_placeUnder (k := (P.curve x).F) hvu, mul_comm]
  refine padicValNat_mul_le_wildConst hℓ h7 (residueChar_prime v)
    ((relRamIdx_dvd_finrank hvw).trans (R.finrank_torsionField_dvd hℓ))
    ((relRamIdx_dvd_finrank hwu).trans (finrank_tpd_dvd P x)) ?_
  intro hpℓ
  by_cases h2 : residueChar v = 2
  · rw [h2]
    exact not_two_dvd_relRamIdx_torsionField P x R v hℓ hℓ2 h2
  · exact not_dvd_relRamIdx_torsionField_of_ne_two P x R hℓ hℓ2 v h2 hpℓ

end AbcAdaptation.Tripod
