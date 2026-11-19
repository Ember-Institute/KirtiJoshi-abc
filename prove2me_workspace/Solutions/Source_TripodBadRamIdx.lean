/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original paths and revisions
Iut/Tripod/BadRamIdx.lean at 10e40d2e52a8e7220c2a90ff1595f5b385f987ef
Iut/Tower/InertiaBound.lean at 9633c1cfca59895aff7c52e836464d9659abf445
Iut/Tower/WildBound.lean at f35eebabf24b1b75c4e68b2a8f8872c5f9961ecb
-/
import Solutions.Source_TripodUnramified
import Solutions.Source_TripodInertiaUnipotent
import Solutions.Source_TripodTorsionDegree
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

universe u

/-- The torsion field degree divides the order of the general linear group. -/
theorem finrank_torsionField_dvd {C : EllipticCurveData.{u}} {ℓ : ℕ}
    (R : C.ModEllRepData ℓ) (hℓ : ℓ.Prime) :
    Module.finrank C.F ↥R.torsionField ∣ (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : FiniteDimensional C.F ↥R.torsionField := Module.Finite.of_restrictScalars_finite ℚ _ _
  rw [← IsGalois.card_aut_eq_finrank C.F ↥R.torsionField, ← R.card_range,
    ← Tripod.card_GL_two ℓ]
  exact Subgroup.card_subgroup_dvd_card R.rep.range

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

theorem card_le_of_forall_pow_eq_one {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (p m : ℕ) [hp : Fact p.Prime] (hG : Nat.card G ∣ p * m) (hpm : ¬ p ∣ m)
    (hH : ∀ σ ∈ H, σ ^ p = 1) : Nat.card H ≤ p := by
  have hP : IsPGroup p H := fun σ => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hH σ.1 σ.2)⟩
  obtain ⟨n, horder⟩ := IsPGroup.iff_card.mp hP
  have hdvd : p ^ n ∣ p * m := horder ▸ (H.card_subgroup_dvd_card.trans hG)
  rw [horder]
  by_cases hn : n = 0
  · rw [hn, pow_zero]
    exact hp.out.one_lt.le
  · have hn1 : n = 1 := by
      by_contra hne
      have hp2 : p ^ 2 ∣ p * m := (pow_dvd_pow p (show 2 ≤ n by omega)).trans hdvd
      rw [sq] at hp2
      exact hpm ((Nat.mul_dvd_mul_iff_left hp.out.pos).mp hp2)
    simpa only [hn1, pow_one] using (le_rfl : p ≤ p)

private lemma not_dvd_gl_cofactor {ℓ : ℕ} (hℓ : ℓ.Prime) : ¬ ℓ ∣ (ℓ ^ 2 - 1) * (ℓ - 1) := by
  intro hdvd
  have h2 := hℓ.two_le
  rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with hdvd | hdvd
  · have hpow : ℓ ∣ ℓ ^ 2 := dvd_pow_self ℓ two_ne_zero
    have hone := Nat.dvd_sub hpow hdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at hone
    exact hℓ.not_dvd_one hone
  · have hle := Nat.le_of_dvd (by omega) hdvd
    omega

private lemma card_GL_two_factor (ℓ : ℕ) :
    (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) = ℓ * ((ℓ ^ 2 - 1) * (ℓ - 1)) := by
  have hfactor : ℓ ^ 2 - ℓ = ℓ * (ℓ - 1) := by rw [Nat.mul_sub, mul_one, sq]
  rw [hfactor, mul_left_comm]

variable (P : CurveProviders) (x : Pt)

/-- At a place above `badT`, at least one of the two Legendre parameters is a nonunit. -/
lemma valuation_genT_ne_one_of_mem_badT {L : Type} [Field L] [NumberField L] [Algebra (tpd P x) L]
    {v : FinitePlace L} {u : FinitePlace (tpd P x)}
    (hvu : FinitePlace.LiesOver v u) (hu : u ∈ badT P x) :
    v.maximalIdeal.valuation L (algebraMap (tpd P x) L (genT P x)) ≠ 1 ∨
      v.maximalIdeal.valuation L (algebraMap (tpd P x) L (genT P x - 1)) ≠ 1 := by
  have hunit (a : tpd P x) : u a = 1 ↔
      v.maximalIdeal.valuation L (algebraMap (tpd P x) L a) = 1 := by
    rw [valuation_map_eq_one_iff hvu a, ← FinitePlace.norm_embedding_eq, norm_eq_one_iff_valued,
      FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']
  change u (genT P x) ≠ 1 ∨ u (genT P x - 1) ≠ 1 at hu
  rcases hu with h | h
  · exact Or.inl fun hval => h ((hunit (genT P x)).mpr hval)
  · exact Or.inr fun hval => h ((hunit (genT P x - 1)).mpr hval)

variable {ℓ : ℕ} (R : (P.curve x).ModEllRepData ℓ)

noncomputable local instance (priority := 1100) : DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

private lemma valuation_genC_ne_one_of_mem_badT (v : FinitePlace ↥R.torsionField)
    (hu : placeTpd (P.curve x).F (P.curve x).E R.torsionField v ∈ badT P x) :
    v.maximalIdeal.valuation _ (algebraMap (P.curve x).F ↥R.torsionField (genC' P x)) ≠ 1 ∨
      v.maximalIdeal.valuation _
        (algebraMap (P.curve x).F ↥R.torsionField (genC' P x) - 1) ≠ 1 := by
  simpa only [IsScalarTower.algebraMap_apply (tpd P x) (P.curve x).F ↥R.torsionField,
    algebraMap_genT, map_sub, map_one] using
      valuation_genT_ne_one_of_mem_badT P x (liesOver_placeTpd v) hu

/-- At bad places away from 2 and ℓ, every inertia automorphism in K/F has ℓ-th power one. -/
theorem inertia_pow_eq_one_of_badT (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (v : FinitePlace ↥R.torsionField) (h2 : residueChar v ≠ 2) (hpℓ : residueChar v ≠ ℓ)
    (hu : placeTpd (P.curve x).F (P.curve x).E R.torsionField v ∈ badT P x)
    (σ : ↥R.torsionField ≃ₐ[(P.curve x).F] ↥R.torsionField)
    (hσ : σ ∈ v.maximalIdeal.asIdeal.inertia (↥R.torsionField ≃ₐ[(P.curve x).F] ↥R.torsionField)) :
    σ ^ ℓ = 1 := by
  let i := algebraMap (P.curve x).F ↥R.torsionField (sqrtNegOne' P x)
  let u := algebraMap (P.curve x).F ↥R.torsionField (sqrtLam' P x)
  have hi : i ^ 2 = -1 := by
    dsimp only [i]
    rw [← map_pow, sqrtNegOne'_sq, map_neg, map_one]
  have hu' : u ^ 2 = algebraMap (P.curve x).F ↥R.torsionField (genC' P x) := by
    dsimp only [u]
    rw [← map_pow, sqrtLam'_sq]
  refine R.eq_one_of_forall_torsion (σ ^ ℓ) fun Q hQ => ?_
  let Q' : (Affine.baseChange (legendre (genC' P x)) ↥R.torsionField).Point := Q
  change Point.map (W' := legendre (genC' P x)) (S := (P.curve x).F) (σ ^ ℓ).toAlgHom Q' = Q'
  refine (point_map_pow (legendre (genC' P x)) σ ℓ Q').trans ?_
  exact iterate_map_eq_self_of_inertia (genC' P x) v h2 (hℓ.odd_of_ne_two hℓ2)
    ((valuation_natCast_eq_one_iff v hℓ).2 hpℓ) (valuation_genC_ne_one_of_mem_badT P x R v hu)
    σ hσ hi hu' (σ.commutes _) (σ.commutes _) Q' hQ

/-- The ramification index in the torsion field is at most ℓ away from 2 and ℓ. -/
theorem relRamIdx_torsionField_le (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (v : FinitePlace ↥R.torsionField) (h2 : residueChar v ≠ 2) (hpℓ : residueChar v ≠ ℓ) :
    relRamIdx v (placeUnder (k := (P.curve x).F) v) ≤ ℓ := by
  let u := placeTpd (P.curve x).F (P.curve x).E R.torsionField v
  let w := placeUnder (k := (P.curve x).F) v
  have hvu : FinitePlace.LiesOver v u :=
    liesOver_placeTpd (F := (P.curve x).F) (E := (P.curve x).E) (L := R.torsionField) v
  have hvw : FinitePlace.LiesOver v w := liesOver_placeUnder v
  have hwu : FinitePlace.LiesOver w u := liesOver_placeUnder_of_liesOver (k := (P.curve x).F) hvu
  change relRamIdx v w ≤ ℓ
  by_cases hu : u ∈ badT P x
  · letI : Fact ℓ.Prime := ⟨hℓ⟩
    letI : FiniteDimensional (P.curve x).F ↥R.torsionField :=
      Module.Finite.of_restrictScalars_finite ℚ _ _
    rw [relRamIdx_eq_card_inertia hvw]
    refine card_le_of_forall_pow_eq_one _ ℓ ((ℓ ^ 2 - 1) * (ℓ - 1)) ?_
      (not_dvd_gl_cofactor hℓ) (inertia_pow_eq_one_of_badT P x R hℓ hℓ2 v h2 hpℓ hu)
    rw [IsGalois.card_aut_eq_finrank, ← card_GL_two_factor]
    exact R.finrank_torsionField_dvd hℓ
  · rw [relRamIdx_torsion_eq_one_at_good_place P x R hℓ hℓ2 hvw hwu h2 hpℓ hu]
    exact hℓ.one_lt.le

end AbcAdaptation.Tripod
