/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/Unramified.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound
import Solutions.Source_ReferenceIutTowerTorsionRigid
import Solutions.Source_ReferenceIutTowerLocalFacts
import Solutions.Source_TripodLogCond
import Solutions.Source_TripodTorsionAction
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical WithZero

section Valuation

variable {L : Type*} [Field L] [NumberField L]

/-- A rational prime is a unit at a finite place precisely away from its residue characteristic. -/
lemma valuation_natCast_eq_one_iff (w : FinitePlace L) {q : ℕ} (hq : q.Prime) :
    w.maximalIdeal.valuation L (q : L) = 1 ↔ residueChar w ≠ q := by
  rw [← map_natCast (algebraMap (𝓞 L) L), valuation_eq_one_iff_notMem,
    natCast_mem_maximalIdeal_iff w hq]
  simp only [AbcAdaptation.Reference.Iut.residueChar, AbcAdaptation.Tripod.residueChar]

/-- Valuation one is preserved by the embedding at a place lying over the given place. -/
lemma valuation_map_eq_one_iff {T : Type*} [Field T] [NumberField T] [Algebra T L]
    {w : FinitePlace L} {u : FinitePlace T} (hwu : FinitePlace.LiesOver w u) (a : T) :
    w.maximalIdeal.valuation L (algebraMap T L a) = 1 ↔ u.maximalIdeal.valuation T a = 1 := by
  rw [valuation_algebraMap_eq_pow hwu]
  exact pow_eq_one_iff_of_nonneg zero_le (ramificationIdx'_ne_zero hwu)

end Valuation

lemma legendre_baseChange {T L : Type*} [Field T] [Field L] [Algebra T L] (a : T) :
    Affine.baseChange (legendre a) L = legendre (algebraMap T L a) := by
  change (legendre a).map (algebraMap T L) = _
  ext <;> simp [legendre, WeierstrassCurve.map]

variable (P : CurveProviders) (x : Pt)

/-- The three square roots included in the original field of definition. -/
noncomputable def sqrtNegOne' : (P.curve x).F :=
  ⟨sqrtNegOne, IntermediateField.subset_adjoin ℚ _
    (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))⟩

noncomputable def sqrtLam' : (P.curve x).F :=
  ⟨sqrtLam x.1, IntermediateField.subset_adjoin ℚ _
    (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))⟩

noncomputable def sqrtOneSubLam' : (P.curve x).F :=
  ⟨sqrtOneSubLam x.1, IntermediateField.subset_adjoin ℚ _
    (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))))))⟩

@[simp] lemma sqrtNegOne'_sq : (sqrtNegOne' P x : (P.curve x).F) ^ 2 = -1 :=
  Subtype.ext sqrtNegOne_sq

@[simp] lemma sqrtLam'_sq : (sqrtLam' P x : (P.curve x).F) ^ 2 = genC' P x :=
  Subtype.ext (sqrtLam_sq x.1)

@[simp] lemma sqrtOneSubLam'_sq : (sqrtOneSubLam' P x : (P.curve x).F) ^ 2 = 1 - genC' P x :=
  Subtype.ext (sqrtOneSubLam_sq x.1)

lemma torsionCoords_three_subset_fieldOf' (l : Qbar) : torsionCoords l 3 ⊆ (fieldOf' l : Set Qbar) :=
  fun _ hc => IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inr hc))

lemma torsionCoords_five_subset_fieldOf' (l : Qbar) : torsionCoords l 5 ⊆ (fieldOf' l : Set Qbar) :=
  fun _ hc => IntermediateField.subset_adjoin ℚ _ (Or.inr hc)

private lemma nsmul_some_eq_zero_of_eq {L : Type*} [Field L]
    {W W' : Affine L} (hWW' : W = W') {a b : L}
    (h : W.Nonsingular a b) (h' : W'.Nonsingular a b) (n : ℕ)
    (hn : n • Point.some a b h = 0) : n • Point.some a b h' = 0 := by
  subst W'
  exact hn

section GoodModel

variable {L : Type} [Field L] [NumberField L] [Algebra (tpd P x) L]
  (w : FinitePlace L)

/-- The valuation hypotheses of `Iut.map_eq_self_of_nsmul_eq_zero` for the Legendre model of
`λ ∈ F_tpd` at a place `w` of an extension `L` of `F_tpd` with `w(λ) = w(λ − 1) = w(2) = 1`. -/
lemma legendre_genT_good (h2 : w.maximalIdeal.valuation L 2 = 1)
    (hl : w.maximalIdeal.valuation L (algebraMap (tpd P x) L (genT P x)) = 1)
    (hl1 : w.maximalIdeal.valuation L (algebraMap (tpd P x) L (genT P x - 1)) = 1) :
    w.maximalIdeal.valuation L (algebraMap (tpd P x) L (legendre (genT P x)).a₂) ≤ 1 ∧
    w.maximalIdeal.valuation L (algebraMap (tpd P x) L (legendre (genT P x)).a₄) ≤ 1 ∧
    w.maximalIdeal.valuation L (algebraMap (tpd P x) L (legendre (genT P x)).a₆) ≤ 1 ∧
    w.maximalIdeal.valuation L (algebraMap (tpd P x) L (legendre (genT P x)).Δ) = 1 := by
  set v := w.maximalIdeal.valuation L
  refine ⟨?_, hl.le, by simp [legendre], ?_⟩
  · change v (algebraMap (tpd P x) L (-(1 + genT P x))) ≤ 1
    rw [map_neg, map_add, map_one, Valuation.map_neg]
    exact (Valuation.map_add _ _ _).trans (max_le (by rw [map_one]) hl.le)
  · have h16 : v (algebraMap (tpd P x) L 16) = 1 := by
      have : (algebraMap (tpd P x) L 16) = 2 ^ 4 := by
        rw [map_ofNat]; norm_num
      rw [this, map_pow, h2, one_pow]
    simp only [legendre_Δ, map_mul, map_pow, hl, hl1, h16, one_pow, mul_one]

end GoodModel

/-! ### The generators of `F/F_tpd` -/

/-- The generators `√−1, √λ, √(1 − λ)` and the coordinates of the `3`- and `5`-torsion of
`F = F_λ` over `F_tpd = ℚ(λ)`. -/
def tpdGens : Set (P.curve x).F :=
  {sqrtNegOne' P x, sqrtLam' P x, sqrtOneSubLam' P x} ∪
    {c | Subtype.val c ∈ torsionCoords x.1 3} ∪ {c | Subtype.val c ∈ torsionCoords x.1 5}

/-- The subfield `F_tpd(√−1, √λ, √(1 − λ), E[3], E[5])` of `F`. -/
noncomputable abbrev tpdAdjoin : IntermediateField (tpd P x) (P.curve x).F :=
  IntermediateField.adjoin (tpd P x) (tpdGens P x)

/-- **`F = F_tpd(√−1, √λ, √(1 − λ), E[3], E[5])`.** -/
theorem adjoin_tpdGens : tpdAdjoin P x = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨t, ht⟩ -
  refine IntermediateField.adjoin_induction (F := ℚ) (E := Qbar)
    (s := ({x.1, sqrtNegOne, sqrtLam x.1, sqrtOneSubLam x.1} ∪ torsionCoords x.1 3 ∪
      torsionCoords x.1 5))
    (p := fun y hy => (⟨y, hy⟩ : (P.curve x).F) ∈ tpdAdjoin P x) ?_ ?_ ?_ ?_ ?_ ht
  · intro y hy
    rcases hy with (hy | hy) | hy
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · have hmem : algebraMap (tpd P x) (P.curve x).F (genT P x) ∈ tpdAdjoin P x :=
          IntermediateField.algebraMap_mem _ _
        exact hmem
      · exact IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (Set.mem_insert _ _)))
      · exact IntermediateField.subset_adjoin _ _
          (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      · exact IntermediateField.subset_adjoin _ _
          (Or.inl (Or.inl (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
    · exact IntermediateField.subset_adjoin _ _ (Or.inl (Or.inr hy))
    · exact IntermediateField.subset_adjoin _ _ (Or.inr hy)
  · intro r
    have hmem : algebraMap (tpd P x) (P.curve x).F (algebraMap ℚ (tpd P x) r) ∈ tpdAdjoin P x :=
      IntermediateField.algebraMap_mem _ _
    rw [← IsScalarTower.algebraMap_apply] at hmem
    exact hmem
  · intro y z _ _ hy hz
    exact add_mem hy hz
  · intro y _ hy
    exact inv_mem hy
  · intro y z _ _ hy hz
    exact mul_mem hy hz

/-- **The Legendre curve of `λ ∈ F_tpd` base changed to `ℚ̄` is `E_λ`.** -/
theorem baseChange_legendre_genT_Fbar :
    Affine.baseChange (legendre (genT P x)) (P.curve x).Fbar = legendre x.1 := by
  rw [legendre_baseChange, IsScalarTower.algebraMap_apply (tpd P x) (P.curve x).F, algebraMap_genT] <;> rfl

/-- **The Legendre curve of `λ ∈ F_tpd` base changed to `F` is `E_λ/F`.** -/
theorem baseChange_legendre_genT :
    Affine.baseChange (legendre (genT P x)) (P.curve x).F = (legendre (genC' P x)).toAffine := by
  rw [legendre_baseChange, algebraMap_genT]

/-! ### Rigidity of the generators at a good place -/

variable {P x}

/-- **The `n`-torsion coordinates are fixed by the inertia group at a good place** (`n` odd,
`p ∤ 2n`, `λ` and `λ − 1` units). -/
theorem torsionCoord_fixed {n : ℕ} (hodd : Odd n)
    (hsub : torsionCoords x.1 n ⊆ (fieldOf' x.1 : Set Qbar)) {w : FinitePlace (P.curve x).F}
    (h2 : residueChar w ≠ 2) (hn : w.maximalIdeal.valuation _ (n : (P.curve x).F) = 1)
    (hl : w.maximalIdeal.valuation _ (genC' P x) = 1)
    (hl1 : w.maximalIdeal.valuation _ (genC' P x - 1) = 1)
    (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)
    (hσ : ∀ z, w.maximalIdeal.valuation _ z ≤ 1 → w.maximalIdeal.valuation _ (σ z - z) < 1)
    {c : Qbar} (hc : c ∈ torsionCoords x.1 n) (hcF : c ∈ fieldOf' x.1) :
    σ ⟨c, hcF⟩ = ⟨c, hcF⟩ := by
  obtain ⟨Q, hQ, hcQ⟩ := Set.mem_iUnion₂.mp hc
  cases Q with
  | zero => exact absurd hcQ (Set.notMem_empty c)
  | some x₀ y₀ h₀ =>
    have hQ' : n • Affine.Point.some x₀ y₀ h₀ = 0 := hQ
    have hx₀ : x₀ ∈ fieldOf' x.1 :=
      hsub (mem_torsionCoords hQ' (by change x₀ ∈ ({x₀, y₀} : Set Qbar); simp))
    have hy₀ : y₀ ∈ fieldOf' x.1 :=
      hsub (mem_torsionCoords hQ' (by change y₀ ∈ ({x₀, y₀} : Set Qbar); simp))
    let xF : (P.curve x).F := ⟨x₀, hx₀⟩
    let yF : (P.curve x).F := ⟨y₀, hy₀⟩
    have hcurve := baseChange_legendre_genT_Fbar P x
    set ι := IsScalarTower.toAlgHom (tpd P x) (P.curve x).F (P.curve x).Fbar
    have hns' : (Affine.baseChange (legendre (genT P x)) (P.curve x).Fbar).Nonsingular (ι xF)
        (ι yF) := by
      rw [hcurve]; exact h₀
    have hnsF : (Affine.baseChange (legendre (genT P x)) (P.curve x).F).Nonsingular xF yF :=
      (Affine.baseChange_nonsingular (W := legendre (genT P x)) ι.injective _ _).mp hns'
    have hQF : n • Affine.Point.some xF yF hnsF = 0 := by
      apply Affine.Point.map_injective (W' := legendre (genT P x)) (S := tpd P x) ι
      rw [map_nsmul, Affine.Point.map_some, map_zero]
      exact nsmul_some_eq_zero_of_eq hcurve.symm h₀ hns' n hQ'
    have h2' := valuation_two_eq_one_of_ne h2
    obtain ⟨ha₂, ha₄, ha₆, hΔ⟩ := legendre_genT_good P x w h2' (by rw [algebraMap_genT]; exact hl)
      (by rw [map_sub, map_one, algebraMap_genT]; exact hl1)
    have hfix := map_eq_self_of_nsmul_eq_zero (w.maximalIdeal.valuation _) (legendre (genT P x))
      rfl rfl ha₂ ha₄ ha₆ hΔ h2' hodd hn (σ : (P.curve x).F →ₐ[tpd P x] (P.curve x).F) hσ _ hQF
    rw [Affine.Point.map_some] at hfix
    obtain ⟨hfx, hfy⟩ := Affine.Point.some.inj hfix
    change c ∈ ({x₀, y₀} : Set Qbar) at hcQ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hcQ
    rcases hcQ with hc | hc
    · have hc' : (⟨c, hcF⟩ : (P.curve x).F) = xF := Subtype.ext hc
      rw [hc']
      exact hfx
    · have hc' : (⟨c, hcF⟩ : (P.curve x).F) = yF := Subtype.ext hc
      rw [hc']
      exact hfy

/-- **The generators of `F/F_tpd` are fixed by the inertia group at a good place** of residue
characteristic `∉ {2, 3, 5}`. -/
theorem tpdGens_fixed {w : FinitePlace (P.curve x).F}
    (h2 : residueChar w ≠ 2) (h3 : residueChar w ≠ 3) (h5 : residueChar w ≠ 5)
    (hl : w.maximalIdeal.valuation _ (genC' P x) = 1)
    (hl1 : w.maximalIdeal.valuation _ (genC' P x - 1) = 1)
    (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)
    (hσ : ∀ z, w.maximalIdeal.valuation _ z ≤ 1 → w.maximalIdeal.valuation _ (σ z - z) < 1) :
    ∀ s ∈ tpdGens P x, σ s = s := by
  have h2' := valuation_two_eq_one_of_ne h2
  intro s hs
  rcases hs with (hs | hs) | hs
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · have hsq : (sqrtNegOne' P x : (P.curve x).F) ^ 2 =
          algebraMap (tpd P x) (P.curve x).F (-1) := by
        rw [map_neg, map_one]; exact sqrtNegOne'_sq P x
      have ha : w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (-1)) = 1 := by
        rw [map_neg, map_one, Valuation.map_neg, map_one]
      exact sqrt_fixed_of_valuation_sub_lt _ (σ : (P.curve x).F →+* (P.curve x).F) hsq
        (σ.commutes _) ha h2'
        (hσ _ (valuation_eq_one_of_sq _ ((congrArg _ hsq).trans ha)).le)
    · have hsq : (sqrtLam' P x : (P.curve x).F) ^ 2 =
          algebraMap (tpd P x) (P.curve x).F (genT P x) := by
        rw [algebraMap_genT]; exact sqrtLam'_sq P x
      have ha : w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (genT P x)) = 1 := by
        rw [algebraMap_genT]; exact hl
      exact sqrt_fixed_of_valuation_sub_lt _ (σ : (P.curve x).F →+* (P.curve x).F) hsq
        (σ.commutes _) ha h2'
        (hσ _ (valuation_eq_one_of_sq _ ((congrArg _ hsq).trans ha)).le)
    · have hsq : (sqrtOneSubLam' P x : (P.curve x).F) ^ 2 =
          algebraMap (tpd P x) (P.curve x).F (1 - genT P x) := by
        rw [map_sub, map_one, algebraMap_genT]; exact sqrtOneSubLam'_sq P x
      have ha : w.maximalIdeal.valuation _
          (algebraMap (tpd P x) (P.curve x).F (1 - genT P x)) = 1 := by
        rw [map_sub, map_one, algebraMap_genT, Valuation.map_sub_swap]; exact hl1
      exact sqrt_fixed_of_valuation_sub_lt _ (σ : (P.curve x).F →+* (P.curve x).F) hsq
        (σ.commutes _) ha h2'
        (hσ _ (valuation_eq_one_of_sq _ ((congrArg _ hsq).trans ha)).le)
  · exact torsionCoord_fixed (by decide) (torsionCoords_three_subset_fieldOf' x.1) h2
      ((valuation_natCast_eq_one_iff w Nat.prime_three).2 h3) hl hl1 σ hσ hs s.2
  · exact torsionCoord_fixed (by decide) (torsionCoords_five_subset_fieldOf' x.1) h2
      ((valuation_natCast_eq_one_iff w Nat.prime_five).2 h5)
      hl hl1 σ hσ hs s.2

/-! ### `F/F_tpd` and `K/F` are unramified at the good places -/

/-- `F/F_tpd` is Galois. -/
theorem isGalois_tpd_curve' : IsGalois (tpd P x) (P.curve x).F := by
  haveI : IsGalois ↥(fieldOfModuli (P.curve x).F (P.curve x).E) (P.curve x).F :=
    ((P.arith x).galois_deg_prime 7 Nat.prime_seven le_rfl).1
  exact IsGalois.tower_top_of_isGalois ↥(fieldOfModuli (P.curve x).F (P.curve x).E) (tpd P x)
    (P.curve x).F

/-- Both Legendre parameters are units at a place above a place outside the conductor support. -/
lemma valuation_genC_eq_one_of_not_mem_badT (P : CurveProviders) (x : Pt)
    {w : FinitePlace (P.curve x).F} {u : FinitePlace (tpd P x)}
    (hwu : FinitePlace.LiesOver w u) (hu : u ∉ badT P x) :
    w.maximalIdeal.valuation _ (genC' P x) = 1 ∧
      w.maximalIdeal.valuation _ (genC' P x - 1) = 1 := by
  change ¬ (u (genT P x) ≠ 1 ∨ u (genT P x - 1) ≠ 1) at hu
  obtain ⟨hLam, hLamSubOne⟩ := not_or.mp hu
  have hunit (a : tpd P x) (ha : u a = 1) : u.maximalIdeal.valuation _ a = 1 := by
    rw [← FinitePlace.norm_embedding_eq, norm_eq_one_iff_valued,
      FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation'] at ha
    exact ha
  constructor
  · rw [← algebraMap_genT P x, valuation_map_eq_one_iff hwu]
    exact hunit _ (not_not.mp hLam)
  · rw [← algebraMap_genT P x, ← map_one (algebraMap (tpd P x) (P.curve x).F), ← map_sub,
      valuation_map_eq_one_iff hwu]
    exact hunit _ (not_not.mp hLamSubOne)

/-- **`F/F_tpd` is unramified at the places of residue characteristic `∉ {2, 3, 5}` over a place
of `F_tpd` at which `λ` and `λ − 1` are units.** -/
theorem relRamIdx_placeUnder_eq_one {w : FinitePlace (P.curve x).F}
    {𝔭 : FinitePlace (tpd P x)} (hw𝔭 : FinitePlace.LiesOver w 𝔭) (h2 : residueChar w ≠ 2)
    (h3 : residueChar w ≠ 3) (h5 : residueChar w ≠ 5) (h𝔭 : 𝔭 ∉ badT P x) :
    relRamIdx w 𝔭 = 1 := by
  haveI := isGalois_tpd_curve' (P := P) (x := x)
  obtain ⟨hl, hl1⟩ := valuation_genC_eq_one_of_not_mem_badT P x hw𝔭 h𝔭
  exact relRamIdx_eq_one_of_inertia_trivial hw𝔭 fun σ hσ =>
    algEquiv_eq_one_of_fixed (adjoin_tpdGens P x) σ (tpdGens_fixed h2 h3 h5 hl hl1 σ hσ)

end AbcAdaptation.Tripod
