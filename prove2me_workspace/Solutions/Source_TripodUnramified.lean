/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/Unramified.lean
-/
import Solutions.Source_ReferenceIutTorsionFaithful
import Solutions.Source_TripodUnramifiedBase

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField WeierstrassCurve
open scoped Classical

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (R : (P.curve x).ModEllRepData ℓ)

lemma relRamIdx_torsion_eq_one_at_good_place (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {v : FinitePlace ↥R.torsionField} {w : FinitePlace (P.curve x).F}
    {u : FinitePlace (tpd P x)} (hvw : FinitePlace.LiesOver v w) (hwu : FinitePlace.LiesOver w u)
    (h2 : residueChar v ≠ 2) (hpℓ : residueChar v ≠ ℓ) (hu : u ∉ badT P x) :
    relRamIdx v w = 1 := by
  obtain ⟨hLam, hLamSubOne⟩ := valuation_genC_eq_one_of_not_mem_badT P x hwu hu
  have hmap (a : tpd P x) : algebraMap (tpd P x) ↥R.torsionField a =
      algebraMap (P.curve x).F ↥R.torsionField (algebraMap (tpd P x) (P.curve x).F a) :=
    IsScalarTower.algebraMap_apply (tpd P x) (P.curve x).F ↥R.torsionField a
  have hl : v.maximalIdeal.valuation _ (algebraMap (tpd P x) ↥R.torsionField (genT P x)) = 1 := by
    rw [hmap, algebraMap_genT, valuation_map_eq_one_iff hvw]
    exact hLam
  have hl1 : v.maximalIdeal.valuation _
      (algebraMap (tpd P x) ↥R.torsionField (genT P x - 1)) = 1 := by
    rw [hmap, map_sub, map_one, algebraMap_genT]
    exact (valuation_map_eq_one_iff hvw _).2 hLamSubOne
  have hW : (legendre (genT P x)).map (algebraMap (tpd P x) (P.curve x).F) = (P.curve x).E :=
    baseChange_legendre_genT P x
  obtain ⟨ha₂, ha₄, ha₆, hΔ⟩ := legendre_genT_good P x v (valuation_two_eq_one_of_ne h2) hl hl1
  rw [hmap, ← WeierstrassCurve.map_a₂, hW] at ha₂
  rw [hmap, ← WeierstrassCurve.map_a₄, hW] at ha₄
  rw [hmap, ← WeierstrassCurve.map_a₆, hW] at ha₆
  rw [hmap, ← WeierstrassCurve.map_Δ, hW] at hΔ
  exact relRamIdx_eq_one_of_torsion hvw (P.curve x).E rfl rfl ha₂ ha₄ ha₆ hΔ h2
    (hℓ.odd_of_ne_two hℓ2) ((valuation_natCast_eq_one_iff v hℓ).2 hpℓ) R.eq_one_of_forall_torsion

/-- The torsion field is unramified over the tripodal field at places of residue
characteristic outside `2, 3, 5, ℓ` whose tripodal place is outside the selected bad set. -/
theorem relRamIdx_torsion_tpd_eq_one (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (v : FinitePlace ↥R.torsionField)
    (hp : AbcAdaptation.Reference.Iut.residueChar v ∉ ({2, 3, 5, ℓ} : Finset ℕ))
    (hgood : ¬ IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ)
      (placeTpd (P.curve x).F (P.curve x).E R.torsionField v)) :
    relRamIdx v (placeTpd (P.curve x).F (P.curve x).E R.torsionField v) = 1 := by
  change residueChar v ∉ ({2, 3, 5, ℓ} : Finset ℕ) at hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  let u := placeTpd (P.curve x).F (P.curve x).E R.torsionField v
  let w := placeUnder (k := (P.curve x).F) v
  have hvu : FinitePlace.LiesOver v u :=
    liesOver_placeTpd (F := (P.curve x).F) (E := (P.curve x).E) (L := R.torsionField) v
  have hvw : FinitePlace.LiesOver v w := liesOver_placeUnder v
  have hwu : FinitePlace.LiesOver w u := liesOver_placeUnder_of_liesOver (k := (P.curve x).F) hvu
  have hu : u ∉ badT P x := by
    intro hbad
    have hchar := residueChar_eq_of_liesOver hvu
    exact hgood (isBadTpdOf_of_mem_badT P x hbad (fun h => hp.1 (hchar.trans h))
      (fun h => hp.2.2.2 (hchar.trans h)))
  have hchar := residueChar_eq_of_liesOver hvw
  have hF := relRamIdx_placeUnder_eq_one hwu (fun h => hp.1 (hchar.trans h))
    (fun h => hp.2.1 (hchar.trans h)) (fun h => hp.2.2.1 (hchar.trans h)) hu
  have hK := relRamIdx_torsion_eq_one_at_good_place P x R hℓ hℓ2 hvw hwu hp.1 hp.2.2.2 hu
  change relRamIdx v u = 1
  rw [relRamIdx_eq_mul_placeUnder (k := (P.curve x).F) hvu, hF, hK, Nat.one_mul]

end AbcAdaptation.Tripod
