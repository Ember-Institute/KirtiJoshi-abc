/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original paths and revisions
Iut/Tripod/TpdInertia.lean at 04283ddb9192c9fb4d5863ce2cf057741556cbf0
Iut/Tripod/TowerFacts.lean at 2d8f000457da6447fa4df4bfec7365c1a49b6384
-/
import Solutions.Source_TripodBadRamIdx
import Solutions.Source_TripodTpdTorsionRep
import Mathlib.Algebra.GroupWithZero.Units.Fintype

set_option autoImplicit false

/-! At bad places away from 2, 3, and 5, the subgroup of inertia fixing the square roots
acts faithfully on the 3- and 5-torsion. It has order at most 15 and index at most two. -/

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

/-! ### The sign of an automorphism on a square root -/

section Sign

variable {k L : Type*} [Field k] [Field L] [CharZero L] [Algebra k L]

/-- The sign `±1` of `σ ∈ Aut(L/k)` on a square root `s` of an element of `k`. -/
noncomputable def signHom (s : L) (hs : ∃ a : k, s ^ 2 = algebraMap k L a) (hs0 : s ≠ 0) :
    (L ≃ₐ[k] L) →* ℤˣ where
  toFun σ := if σ s = s then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    have key : ∀ ρ : L ≃ₐ[k] L, ρ s = s ∨ ρ s = -s := fun ρ => by
      obtain ⟨a, ha⟩ := hs
      have : (ρ s) ^ 2 = s ^ 2 := by rw [← map_pow, ha, ρ.commutes]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    have hne : -s ≠ s := fun h => hs0 (by
      have h2 : (2 : L) * s = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)
    simp only [AlgEquiv.mul_apply]
    rcases key τ with hτ | hτ
    · simp [hτ]
    · rcases key σ with hσ | hσ
      · simp [hτ, hσ, hne]
      · simp [hτ, hσ, hne]

lemma signHom_eq_one_iff {s : L} (hs : ∃ a : k, s ^ 2 = algebraMap k L a) (hs0 : s ≠ 0)
    (σ : L ≃ₐ[k] L) : signHom s hs hs0 σ = 1 ↔ σ s = s := by
  change (if σ s = s then (1 : ℤˣ) else -1) = 1 ↔ σ s = s
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 h⟩

end Sign

end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

variable (P : CurveProviders) (x : Pt)

set_option quotPrecheck false in
/-- The Legendre curve `E_λ` over `F = F_λ`. -/
local notation "EF" => Affine.baseChange (legendre (genT P x)) (P.curve x).F

/-- `√λ ∈ F`, as a square root of an element of `F_tpd`. -/
lemma sqrtLam'_sq_mem : ∃ a : tpd P x, (sqrtLam' P x : (P.curve x).F) ^ 2 =
    algebraMap (tpd P x) (P.curve x).F a :=
  ⟨genT P x, by rw [algebraMap_genT]; exact sqrtLam'_sq P x⟩

/-- `√(1 − λ) ∈ F`, as a square root of an element of `F_tpd`. -/
lemma sqrtOneSubLam'_sq_mem : ∃ a : tpd P x, (sqrtOneSubLam' P x : (P.curve x).F) ^ 2 =
    algebraMap (tpd P x) (P.curve x).F a :=
  ⟨1 - genT P x, by rw [map_sub, map_one, algebraMap_genT]; exact sqrtOneSubLam'_sq P x⟩

lemma sqrtLam'_ne_zero : sqrtLam' P x ≠ 0 := by
  intro h
  have hsq := sqrtLam'_sq P x
  rw [h, zero_pow two_ne_zero] at hsq
  exact gen'_ne_zero x.2.1 hsq.symm

lemma sqrtOneSubLam'_ne_zero : sqrtOneSubLam' P x ≠ 0 := by
  intro h
  have hsq := sqrtOneSubLam'_sq P x
  rw [h, zero_pow two_ne_zero, eq_comm, sub_eq_zero] at hsq
  exact gen'_ne_one x.2.2 hsq.symm

/-- **The subgroup `I⁺`** of the automorphisms of `F/F_tpd` in the inertia group of `w` fixing
`√λ` and `√(1 − λ)`. -/
noncomputable def inertiaPlus (w : FinitePlace (P.curve x).F) :
    Subgroup ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) :=
  w.maximalIdeal.asIdeal.inertia _ ⊓
    ((signHom _ (sqrtLam'_sq_mem P x) (sqrtLam'_ne_zero P x)).ker ⊓
      (signHom _ (sqrtOneSubLam'_sq_mem P x) (sqrtOneSubLam'_ne_zero P x)).ker)

lemma mem_inertiaPlus_iff (w : FinitePlace (P.curve x).F)
    (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) :
    σ ∈ inertiaPlus P x w ↔ σ ∈ w.maximalIdeal.asIdeal.inertia _ ∧
      σ (sqrtLam' P x) = sqrtLam' P x ∧ σ (sqrtOneSubLam' P x) = sqrtOneSubLam' P x := by
  simp only [inertiaPlus, Subgroup.mem_inf, MonoidHom.mem_ker, signHom_eq_one_iff]

/-! ### `[I : I⁺] ≤ 2` -/

/-- If fixing the square root `f` forces fixing both displayed roots, the sign homomorphism
on `f` has kernel contained in `I⁺`, giving `[I : I⁺] ≤ 2`. -/
theorem card_inertia_le_two_mul (w : FinitePlace (P.curve x).F) (f : (P.curve x).F)
    (hf : ∃ a : tpd P x, f ^ 2 = algebraMap (tpd P x) (P.curve x).F a) (hf0 : f ≠ 0)
    (hplus : ∀ σ ∈ w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F),
      σ f = f → σ (sqrtLam' P x) = sqrtLam' P x ∧ σ (sqrtOneSubLam' P x) = sqrtOneSubLam' P x) :
    Nat.card (w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)) ≤
      2 * Nat.card (inertiaPlus P x w) := by
  haveI : FiniteDimensional (tpd P x) (P.curve x).F :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  let I := w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)
  let ε := (signHom f hf hf0).domRestrict I
  have h1 := Subgroup.card_mul_index ε.ker
  have hidx : ε.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card ε.range ≤ Nat.card ℤˣ := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hker : Nat.card ε.ker ≤ Nat.card (inertiaPlus P x w) := by
    refine Nat.card_le_card_of_injective (fun σ => ⟨σ.1.1, ?_⟩) ?_
    · rw [mem_inertiaPlus_iff]
      have hσf : σ.1.1 f = f :=
        (signHom_eq_one_iff hf hf0 σ.1.1).mp (MonoidHom.mem_ker.mp σ.2)
      exact ⟨σ.1.2, hplus σ.1.1 σ.1.2 hσf⟩
    · intro σ τ h
      have h' := congrArg Subtype.val h
      simp only at h'
      exact Subtype.ext (Subtype.ext h')
  calc Nat.card I = Nat.card ε.ker * ε.ker.index := h1.symm
    _ ≤ Nat.card (inertiaPlus P x w) * 2 := Nat.mul_le_mul hker hidx
    _ = 2 * Nat.card (inertiaPlus P x w) := mul_comm _ _

private lemma inertia_fixes_sqrt_neg_one {w : FinitePlace (P.curve x).F}
    (h2 : residueChar w ≠ 2) (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)
    (hσ : σ ∈ w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)) :
    σ (sqrtNegOne' P x) = sqrtNegOne' P x := by
  have ha : w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (-1)) = 1 := by
    rw [map_neg, map_one, Valuation.map_neg, map_one]
  have hsq : (sqrtNegOne' P x) ^ 2 = algebraMap (tpd P x) (P.curve x).F (-1) := by
    rw [map_neg, map_one, sqrtNegOne'_sq]
  exact sqrt_fixed_of_valuation_sub_lt _ (σ : (P.curve x).F →+* (P.curve x).F) hsq
    (σ.commutes _) ha (valuation_two_eq_one_of_ne h2)
    (valuation_sub_lt_one_of_mem_inertia hσ
      (valuation_eq_one_of_sq _ ((congrArg _ hsq).trans ha)).le)

/-! ### `I⁺` acts unipotently on the `3`- and `5`-torsion -/

/-- **`I⁺` acts unipotently on `E_λ(F)[n]` at a bad place** (`n` odd, `w(n) = 1`, `w(2) = 1`):
`σ^n` fixes the `n`-torsion pointwise for `σ ∈ I⁺`. -/
theorem galF_pow_eq_self_of_mem_inertiaPlus (w : FinitePlace (P.curve x).F)
    (h2 : residueChar w ≠ 2) {n : ℕ} (hodd : Odd n)
    (hn : w.maximalIdeal.valuation _ (n : (P.curve x).F) = 1)
    (hbad : w.maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
      w.maximalIdeal.valuation _ (genC' P x - 1) ≠ 1)
    (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) (hσ : σ ∈ inertiaPlus P x w)
    (Q : (EF).Point) (hQ : n • Q = 0) : galF P x (σ ^ n) Q = Q := by
  rw [mem_inertiaPlus_iff] at hσ
  obtain ⟨hσI, hσa, _⟩ := hσ
  have hi := sqrtNegOne'_sq P x
  have hσi := inertia_fixes_sqrt_neg_one P x h2 σ hσI
  have hu : (sqrtLam' P x : (P.curve x).F) ^ 2 = algebraMap (tpd P x) (P.curve x).F (genT P x) := by
    rw [algebraMap_genT]; exact sqrtLam'_sq P x
  have hbad' : w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (genT P x)) ≠ 1 ∨
      w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (genT P x) - 1) ≠ 1 := by
    rw [algebraMap_genT]; exact hbad
  have := iterate_map_eq_self_of_inertia (genT P x) w h2 hodd hn hbad' σ hσI hi hu hσi hσa Q hQ
  unfold galF
  rw [point_map_pow]
  exact this

/-! ### `|I⁺| ≤ 15` -/

private lemma repF_pow_eq_one_of_mem_inertiaPlus (w : FinitePlace (P.curve x).F)
    (h2 : residueChar w ≠ 2) {n : ℕ} [Fact n.Prime] (hodd : Odd n)
    (hn : w.maximalIdeal.valuation _ (n : (P.curve x).F) = 1)
    (hbad : w.maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
      w.maximalIdeal.valuation _ (genC' P x - 1) ≠ 1)
    (hsub : torsionCoords x.1 n ⊆ (fieldOf' x.1 : Set Qbar)) (σ : inertiaPlus P x w) :
    repF P x n hsub σ.1 ^ n = 1 := by
  have hker : σ.1 ^ n ∈ (repF P x n hsub).ker :=
    (mem_repF_ker_iff P x n hsub (σ.1 ^ n)).mpr
      (galF_pow_eq_self_of_mem_inertiaPlus P x w h2 hodd hn hbad σ.1 σ.2)
  exact (map_pow (repF P x n hsub) σ.1 n).symm.trans (MonoidHom.mem_ker.mp hker)

private lemma eq_one_of_fixes_three_five (w : FinitePlace (P.curve x).F)
    (h2 : residueChar w ≠ 2) (σ : inertiaPlus P x w)
    (h3 : ∀ Q : (EF).Point, 3 • Q = 0 → galF P x σ.1 Q = Q)
    (h5 : ∀ Q : (EF).Point, 5 • Q = 0 → galF P x σ.1 Q = Q) : σ = 1 := by
  obtain ⟨hσI, hσa, hσb⟩ := (mem_inertiaPlus_iff P x w σ.1).mp σ.2
  have hσi := inertia_fixes_sqrt_neg_one P x h2 σ.1 hσI
  apply Subtype.ext
  refine algEquiv_eq_one_of_fixed (adjoin_tpdGens P x) σ.1 fun s hs => ?_
  simp only [tpdGens, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq] at hs
  rcases hs with (hs | hs) | hs
  · rcases hs with rfl | rfl | rfl
    · exact hσi
    · exact hσa
    · exact hσb
  · exact torsionCoord_fixed_of_galF P x 3 (torsionCoords_three_subset_fieldOf' x.1) σ.1 h3 hs s.2
  · exact torsionCoord_fixed_of_galF P x 5 (torsionCoords_five_subset_fieldOf' x.1) σ.1 h5 hs s.2

private lemma card_le_fifteen_of_representations {G : Type*} [Group G]
    (ρ₃ : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (ρ₅ : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5))
    (hpow3 : ∀ σ : G, ρ₃ σ ^ 3 = 1) (hpow5 : ∀ σ : G, ρ₅ σ ^ 5 = 1)
    (hfaithful : ∀ σ : G, ρ₃ σ = 1 → ρ₅ σ = 1 → σ = 1) : Nat.card G ≤ 15 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hGL3 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) ∣ 3 * 16 := by
    rw [card_GL_two 3]
    norm_num
  have hGL5 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) ∣ 5 * 96 := by
    rw [card_GL_two 5]
    norm_num
  have hrange3 : Nat.card ρ₃.range ≤ 3 :=
    card_le_of_forall_pow_eq_one ρ₃.range 3 16 hGL3 (by norm_num) fun τ hτ => by
      obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hτ
      exact hpow3 σ
  let ρ₅' := ρ₅.domRestrict ρ₃.ker
  have hinj : Function.Injective ρ₅' := by
    refine (injective_iff_map_eq_one ρ₅').mpr fun σ hσ => Subtype.ext ?_
    have hσ5 : ρ₅ σ.1 = 1 := by
      simpa only [ρ₅', MonoidHom.domRestrict_apply] using hσ
    exact hfaithful σ.1 (MonoidHom.mem_ker.mp σ.2) hσ5
  have hker3 : Nat.card ρ₃.ker ≤ 5 := by
    calc Nat.card ρ₃.ker ≤ Nat.card ρ₅'.range :=
          Nat.card_le_card_of_injective ρ₅'.rangeRestrict
            (MonoidHom.rangeRestrict_injective_iff.mpr hinj)
      _ ≤ 5 := card_le_of_forall_pow_eq_one ρ₅'.range 5 96 hGL5 (by norm_num) fun τ hτ => by
          obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hτ
          simpa only [ρ₅', MonoidHom.domRestrict_apply] using hpow5 σ.1
  calc Nat.card G = Nat.card ρ₃.ker * ρ₃.ker.index := (Subgroup.card_mul_index ρ₃.ker).symm
    _ = Nat.card ρ₃.ker * Nat.card ρ₃.range := by rw [Subgroup.index_ker]
    _ ≤ 5 * 3 := Nat.mul_le_mul hker3 hrange3
    _ = 15 := by norm_num

/-- **`|I⁺| ≤ 15`** at a bad place of residue characteristic `∉ {2, 3, 5}`. -/
theorem card_inertiaPlus_le (w : FinitePlace (P.curve x).F) (h2 : residueChar w ≠ 2)
    (h3 : residueChar w ≠ 3) (h5 : residueChar w ≠ 5)
    (hbad : w.maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
      w.maximalIdeal.valuation _ (genC' P x - 1) ≠ 1) :
    Nat.card (inertiaPlus P x w) ≤ 15 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsub3 := torsionCoords_three_subset_fieldOf' x.1
  have hsub5 := torsionCoords_five_subset_fieldOf' x.1
  refine card_le_fifteen_of_representations
    ((repF P x 3 hsub3).domRestrict (inertiaPlus P x w))
    ((repF P x 5 hsub5).domRestrict (inertiaPlus P x w)) ?_ ?_ ?_
  · intro σ
    rw [MonoidHom.domRestrict_apply]
    exact repF_pow_eq_one_of_mem_inertiaPlus P x w h2 (n := 3) (by decide)
      ((valuation_natCast_eq_one_iff w Nat.prime_three).2 h3) hbad hsub3 σ
  · intro σ
    rw [MonoidHom.domRestrict_apply]
    exact repF_pow_eq_one_of_mem_inertiaPlus P x w h2 (n := 5) (by decide)
      ((valuation_natCast_eq_one_iff w Nat.prime_five).2 h5) hbad hsub5 σ
  · intro σ hσ3 hσ5
    rw [MonoidHom.domRestrict_apply] at hσ3 hσ5
    exact eq_one_of_fixes_three_five P x w h2 σ
      ((mem_repF_ker_iff P x 3 hsub3 σ.1).mp (MonoidHom.mem_ker.mpr hσ3))
      ((mem_repF_ker_iff P x 5 hsub5 σ.1).mp (MonoidHom.mem_ker.mpr hσ5))

/-! ### `e(w/u) ≤ 30` -/

/-- **`F_λ/ℚ(λ)` has ramification index `≤ 30` at the bad places of residue characteristic
`∉ {2, 3, 5}`.** -/
theorem relRamIdx_tpd_le_thirty {w : FinitePlace (P.curve x).F} {𝔭 : FinitePlace (tpd P x)}
    (hw𝔭 : FinitePlace.LiesOver w 𝔭) (h2 : residueChar w ≠ 2) (h3 : residueChar w ≠ 3)
    (h5 : residueChar w ≠ 5) (h𝔭 : 𝔭 ∈ badT P x) : relRamIdx w 𝔭 ≤ 30 := by
  haveI : IsGalois (tpd P x) (P.curve x).F := isGalois_tpd_curve' (P := P) (x := x)
  set v := w.maximalIdeal.valuation (P.curve x).F
  have h2' : v 2 = 1 := valuation_two_eq_one_of_ne h2
  have hbad : v (genC' P x) ≠ 1 ∨ v (genC' P x - 1) ≠ 1 := by
    simpa only [map_sub, map_one, algebraMap_genT] using
      valuation_genT_ne_one_of_mem_badT P x hw𝔭 h𝔭
  rw [relRamIdx_eq_card_inertia hw𝔭]
  refine le_trans ?_ (Nat.mul_le_mul_left 2 (card_inertiaPlus_le P x w h2 h3 h5 hbad))
  -- the inertia condition and the rigidity of square roots of units
  have hrigid : ∀ (s : (P.curve x).F) (a : tpd P x), s ^ 2 = algebraMap (tpd P x) (P.curve x).F a →
      v (algebraMap (tpd P x) (P.curve x).F a) = 1 →
      ∀ σ ∈ w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F),
        σ s = s := fun s a hs ha σ hσ =>
    sqrt_fixed_of_valuation_sub_lt _ (σ : (P.curve x).F →+* (P.curve x).F) hs (σ.commutes _) ha
      h2' (valuation_sub_lt_one_of_mem_inertia hσ
        (valuation_eq_one_of_sq _ ((congrArg _ hs).trans ha)).le)
  have hu : (sqrtLam' P x : (P.curve x).F) ^ 2 = algebraMap (tpd P x) (P.curve x).F (genT P x) := by
    rw [algebraMap_genT]; exact sqrtLam'_sq P x
  have hb : (sqrtOneSubLam' P x : (P.curve x).F) ^ 2 =
      algebraMap (tpd P x) (P.curve x).F (1 - genT P x) := by
    rw [map_sub, map_one, algebraMap_genT]; exact sqrtOneSubLam'_sq P x
  rcases lt_trichotomy (v (genC' P x)) 1 with hl | hl | hl
  · -- `v(λ) < 1`: `√(1 − λ)` is fixed by `I`; the sign on `√λ` cuts out `I⁺`
    have hunit : v (algebraMap (tpd P x) (P.curve x).F (1 - genT P x)) = 1 := by
      rw [map_sub, map_one, algebraMap_genT, Valuation.map_sub_eq_of_lt_left _ (by
        rw [map_one]; exact hl), map_one]
    exact card_inertia_le_two_mul P x w _ (sqrtLam'_sq_mem P x) (sqrtLam'_ne_zero P x)
      fun σ hσ hf => ⟨hf, hrigid _ _ hb hunit σ hσ⟩
  · -- `v(λ) = 1`, so `v(λ − 1) < 1`: `√λ` is fixed by `I`; the sign on `√(1 − λ)` cuts out `I⁺`
    have hunit : v (algebraMap (tpd P x) (P.curve x).F (genT P x)) = 1 := by
      rw [algebraMap_genT]; exact hl
    exact card_inertia_le_two_mul P x w _ (sqrtOneSubLam'_sq_mem P x) (sqrtOneSubLam'_ne_zero P x)
      fun σ hσ hf => ⟨hrigid _ _ hu hunit σ hσ, hf⟩
  · -- `v(λ) > 1`: `√(1 − λ)/√λ` is fixed by `I`; the sign on `√λ` cuts out `I⁺`
    have hl0 : genC' P x ≠ 0 := gen'_ne_zero x.2.1
    let a : (P.curve x).F := sqrtLam' P x
    let b : (P.curve x).F := sqrtOneSubLam' P x
    have ha0 : a ≠ 0 := sqrtLam'_ne_zero P x
    have hr : (b / a) ^ 2 = algebraMap (tpd P x) (P.curve x).F ((1 - genT P x) / genT P x) := by
      rw [map_div₀, div_pow]
      exact congrArg₂ (· / ·) hb hu
    have hunit : v (algebraMap (tpd P x) (P.curve x).F ((1 - genT P x) / genT P x)) = 1 := by
      rw [map_div₀, map_sub, map_one, algebraMap_genT, map_div₀, Valuation.map_sub_swap,
        Valuation.map_sub_eq_of_lt_left _ (by rw [map_one]; exact hl),
        div_self ((Valuation.ne_zero_iff _).mpr hl0)]
    refine card_inertia_le_two_mul P x w a (sqrtLam'_sq_mem P x) ha0 fun σ hσ hf => ⟨hf, ?_⟩
    have hσr : σ (b / a) = b / a := hrigid _ _ hr hunit σ hσ
    have h1 : σ b / σ a = b / a := (map_div₀ σ b a).symm.trans hσr
    have h2 : σ b / a = b / a :=
      (congrArg (fun t : (P.curve x).F => σ b / t) hf).symm.trans h1
    exact (div_left_inj' ha0).mp h2

variable {ℓ : ℕ} (R : (P.curve x).ModEllRepData ℓ)

/-- The total ramification index is at most `30 * ℓ` away from `2, 3, 5, ℓ`. -/
theorem relRamIdx_le_thirty_mul (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (v : FinitePlace ↥R.torsionField)
    (hp : AbcAdaptation.Reference.Iut.residueChar v ∉ ({2, 3, 5, ℓ} : Finset ℕ)) :
    relRamIdx v (placeTpd (P.curve x).F (P.curve x).E R.torsionField v) ≤ 30 * ℓ := by
  change residueChar v ∉ ({2, 3, 5, ℓ} : Finset ℕ) at hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  obtain ⟨h2, h3, h5, hpℓ⟩ := hp
  let u := placeTpd (P.curve x).F (P.curve x).E R.torsionField v
  let w := placeUnder (k := (P.curve x).F) v
  have hvu : FinitePlace.LiesOver v u :=
    liesOver_placeTpd (F := (P.curve x).F) (E := (P.curve x).E) (L := R.torsionField) v
  have hwu : FinitePlace.LiesOver w u := liesOver_placeUnder_of_liesOver (k := (P.curve x).F) hvu
  have hchar := residueChar_eq_of_liesOver (liesOver_placeUnder (k := (P.curve x).F) v)
  have hw2 : residueChar w ≠ 2 := fun h => h2 (hchar.trans h)
  have hw3 : residueChar w ≠ 3 := fun h => h3 (hchar.trans h)
  have hw5 : residueChar w ≠ 5 := fun h => h5 (hchar.trans h)
  have hF : relRamIdx w u ≤ 30 := by
    by_cases hu : u ∈ badT P x
    · exact relRamIdx_tpd_le_thirty P x hwu hw2 hw3 hw5 hu
    · simpa only [relRamIdx_placeUnder_eq_one hwu hw2 hw3 hw5 hu] using
        (by decide : (1 : ℕ) ≤ 30)
  have hK := relRamIdx_torsionField_le P x R hℓ hℓ2 v h2 hpℓ
  change relRamIdx v u ≤ 30 * ℓ
  rw [relRamIdx_eq_mul_placeUnder (k := (P.curve x).F) hvu]
  exact Nat.mul_le_mul hF hK

end AbcAdaptation.Tripod
