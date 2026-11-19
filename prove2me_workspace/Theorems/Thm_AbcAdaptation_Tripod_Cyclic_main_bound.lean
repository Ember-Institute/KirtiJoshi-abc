/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicIsogeny.lean (compact-bound transport and Cyclic.main_bound)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TripodalPlaceTransport
import Definitions.Def_TripodLegendreHeightBasics
import Solutions.Source_TripodCyclicVeluLog
import Solutions.Source_TripodFinitePrimeCounting

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Cyclic

open AbcAdaptation.Reference.Iut NumberField WeierstrassCurve
open scoped Classical

attribute [local instance 1100] JoshiTeich.ReferenceIut.instDecidableEqIntermediateField

private lemma abs_log_infinite_le (x : Pt) {K : CompactlyBounded}
    (hx : x ∈ K.set) (v : InfinitePlace (fieldOf' x.1)) :
    |Real.log (v (gen' x.1))| ≤ K.c ∧ |Real.log (v (gen' x.1 - 1))| ≤ K.c := by
  have hfield : fieldOf x.1 ≤ fieldOf' x.1 :=
    IntermediateField.adjoin_simple_le_iff.mpr (mem_fieldOfExtended_self x.1)
  let f : fieldOf x.1 →+* fieldOf' x.1 := (IntermediateField.inclusion hfield).toRingHom
  have hgen : f (gen x.1) = gen' x.1 := by
    apply Subtype.ext
    exact coe_gen x.1
  have hsub : f (gen x.1 - 1) = gen' x.1 - 1 := by
    rw [map_sub, map_one, hgen]
  simpa only [InfinitePlace.comap_apply, hgen, hsub] using
    (CompactlyBounded.mem_set.mp hx).2 (v.comap f)

private lemma abs_log_two_le (P : CurveProviders) (x : Pt) {K : CompactlyBounded}
    (hx : x ∈ K.set) (v : FinitePlace (P.curve x).F) (hv : residueChar v = 2) :
    |Real.log (v (genC' P x))| ≤ K.c * localDeg (P.curve x).F v ∧
      |Real.log (v (genC' P x - 1))| ≤ K.c * localDeg (P.curve x).F v := by
  let u : FinitePlace (tpd P x) := AbcAdaptation.Tripod.placeUnder v
  have hvu : FinitePlace.LiesOver v u := liesOver_placeUnder v
  have hu2 : residueChar u = 2 := (residueChar_eq_of_liesOver hvu).symm.trans hv
  have hb := hx.1 (tpdPlace P x u) (by rw [residueChar_tpdPlace, hu2]; exact K.two_mem)
  rw [tpdPlace_gen, tpdPlace_gen_sub_one] at hb
  have hd : (relLocalDeg v u : ℝ) ≤ localDeg (P.curve x).F v := by
    rw [localDeg_eq_mul hvu]
    have hpos : 0 < localDeg (tpd P x) u := Nat.mul_pos (ramIdx_pos' u) (inertDeg_pos' u)
    exact_mod_cast Nat.le_mul_of_pos_left (relLocalDeg v u) hpos
  have hlog (y : tpd P x) : |Real.log (v (algebraMap (tpd P x) (P.curve x).F y))| =
      relLocalDeg v u * |Real.log (u y)| := by
    rw [apply_algebraMap_eq_pow hvu, Real.log_pow, abs_mul, Nat.abs_cast]
  have h₁ := hlog (genT P x)
  have h₂ := hlog (genT P x - 1)
  rw [algebraMap_genT] at h₁
  rw [map_sub, map_one, algebraMap_genT] at h₂
  rw [h₁, h₂]
  constructor
  · exact (mul_le_mul hd hb.1 (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)
  · exact (mul_le_mul hd hb.2 (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)

private lemma sum_neg_log_apply_natCast {F : Type*} [Field F] [NumberField F]
    {n : ℕ} (hn : n ≠ 0) {S : Finset (FinitePlace F)}
    (hS : ∀ v : FinitePlace F, v (n : F) ≠ 1 → v ∈ S) :
    ∑ v ∈ S, -Real.log (v (n : F)) = Module.finrank ℚ F * Real.log n := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hprod : ∏ v ∈ S, v (n : F) = |(Algebra.norm ℚ (n : F) : ℝ)|⁻¹ := by
    have h := FinitePlace.prod_eq_inv_abs_norm hnF
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => hS v hv] at h
    simpa only [Rat.cast_inv, Rat.cast_abs] using h
  have hlog :
      Real.log (∏ v ∈ S, v (n : F)) = ∑ v ∈ S, Real.log (v (n : F)) :=
    Real.log_prod (s := S) (f := fun v => v (n : F))
      (fun v _ => ((FinitePlace.pos_iff (w := v)).mpr hnF).ne')
  have hnorm : (Algebra.norm ℚ (n : F) : ℝ) = (n : ℝ) ^ Module.finrank ℚ F := by
    rw [Algebra.norm_natCast ℚ, Rat.cast_pow, Rat.cast_natCast]
  rw [Finset.sum_neg_distrib, ← hlog, hprod, Real.log_inv, neg_neg, hnorm, abs_pow,
    Nat.abs_cast, Real.log_pow]

private lemma sum_log_j_odd_bad (P : CurveProviders) (x : Pt)
    (S : Finset (FinitePlace (P.curve x).F))
    (hS : ∀ v ∈ (P.arith x).badAll_finite.toFinset, v ∈ S) :
    (∑ v ∈ S.filter (fun v => v ∈ (P.curve x).badAll ∧ residueChar v ≠ 2),
      Real.log (v (P.curve x).E.j)) =
        (Module.finrank ℚ (P.curve x).F : ℝ) * (P.h x - (P.localData x).heightEq 2) := by
  have hfilter :
      S.filter (fun v => v ∈ (P.curve x).badAll ∧ residueChar v ≠ 2) =
        (P.arith x).badAll_finite.toFinset.filter (fun v => residueChar v ≠ 2) := by
    apply Finset.ext
    intro v
    let B := (P.arith x).badAll_finite.toFinset
    have hB : v ∈ B ↔ v ∈ (P.curve x).badAll :=
      (P.arith x).badAll_finite.mem_toFinset
    have hOdd : v ∈ B.filter (fun w => residueChar w ≠ 2) ↔
        v ∈ B ∧ residueChar v ≠ 2 :=
      @Finset.mem_filter _ (fun w => residueChar w ≠ 2)
        (fun w => @instDecidableNot _ (instDecidableEqNat (residueChar w) 2)) B v
    change (v ∈ S.filter (fun w => w ∈ (P.curve x).badAll ∧ residueChar w ≠ 2)) ↔
      v ∈ B.filter (fun w => residueChar w ≠ 2)
    rw [Finset.mem_filter, hOdd, hB]
    exact ⟨And.right, fun hv => ⟨hS v (hB.mpr hv.1), hv⟩⟩
  rw [hfilter]
  exact (finrank_mul_h_sub P x).symm

theorem main_bound {P : CurveProviders} {x : Pt} {ℓ : ℕ} {hℓ : ℓ.Prime}
    {H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))}
    {K : CompactlyBounded} (hx : x ∈ K.set) (hH : Nat.card H = ℓ) (hodd : ℓ ≠ 2)
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H)
    (hgraph : IsGraphLineOdd P x hℓ hodd H) {C₀ : ℝ} (hC₀1 : 1 ≤ C₀)
    (hC₀ : LegendreTorsionXBound K.c C₀) :
    ((ℓ : ℝ) - 1) / 4 * (P.h x - (P.localData x).heightEq 2) ≤
      10 * Real.log ℓ + (2 * Real.log (32 * C₀) + 6 * K.c + 4 * Real.log 4) := by
  let _ : Finite (HL P x hℓ H) := finite_HL P x hℓ H hH
  let _ : Fintype (HL P x hℓ H) := Fintype.ofFinite _
  obtain ⟨ρ, hρ0, hρ, hpf⟩ := exists_ratio_logProductFormula P x hℓ H hH hodd hgal
  let d : ℝ := Module.finrank ℚ (P.curve x).F
  have hd0 : 0 < d := by
    dsimp only [d]
    exact_mod_cast Module.finrank_pos
  have h4 : (4 : (P.curve x).F) ≠ 0 := by norm_num
  have hℓ0 : (ℓ : (P.curve x).F) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  let S : Finset (FinitePlace (P.curve x).F) :=
    (FinitePlace.hasFiniteMulSupport hρ0).toFinset ∪ (P.arith x).badAll_finite.toFinset ∪
      (FinitePlace.hasFiniteMulSupport h4).toFinset ∪ (FinitePlace.hasFiniteMulSupport hℓ0).toFinset
  have hSρ : ∀ v : FinitePlace (P.curve x).F, v ρ ≠ 1 → v ∈ S := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      ((FinitePlace.hasFiniteMulSupport hρ0).mem_toFinset.mpr hv)))
  have hS4 : ∀ v : FinitePlace (P.curve x).F, v ((4 : ℕ) : (P.curve x).F) ≠ 1 → v ∈ S := by
    intro v hv
    have hv' : v (4 : (P.curve x).F) ≠ 1 := by simpa only [Nat.cast_ofNat] using hv
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      ((FinitePlace.hasFiniteMulSupport h4).mem_toFinset.mpr hv'))
  have hSℓ : ∀ v : FinitePlace (P.curve x).F, v (ℓ : (P.curve x).F) ≠ 1 → v ∈ S := fun v hv =>
    Finset.mem_union_right _ ((FinitePlace.hasFiniteMulSupport hℓ0).mem_toFinset.mpr hv)
  have hSbad : ∀ v ∈ (P.arith x).badAll_finite.toFinset, v ∈ S := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  have hlogpf := hpf S hSρ
  have harch (v : InfinitePlace (P.curve x).F) :
      Real.log (v ρ) ≤ 2 * Real.log (32 * C₀) + 6 * Real.log ℓ + K.c := by
    obtain ⟨h₁, h₂⟩ := abs_log_infinite_le x hx v
    exact log_infinite_bound P x hℓ H hρ hH hodd hρ0 hC₀1 hC₀ v h₁ h₂
  have hsum_arch : (∑ v : InfinitePlace (P.curve x).F, (v.mult : ℝ) * Real.log (v ρ)) ≤
      d * (2 * Real.log (32 * C₀) + 6 * Real.log ℓ + K.c) := by
    calc
      _ ≤ ∑ v : InfinitePlace (P.curve x).F,
          (v.mult : ℝ) * (2 * Real.log (32 * C₀) + 6 * Real.log ℓ + K.c) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (harch v) (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  have hfin := Finset.sum_le_sum fun v (_ : v ∈ S) =>
    log_apply_le P x hℓ H hρ hH hodd hgraph hρ0 v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hfin
  have hgain : ∑ v ∈ S, (if v ∈ (P.curve x).badAll ∧ residueChar v ≠ 2 then
      -(((ℓ : ℝ) - 1) / 4 * Real.log (v (P.curve x).E.j)) else 0) =
      -(((ℓ : ℝ) - 1) / 4 * (d * (P.h x - (P.localData x).heightEq 2))) := by
    rw [← Finset.sum_filter, Finset.sum_neg_distrib, ← Finset.mul_sum,
      sum_log_j_odd_bad P x S hSbad]
  have hlog4 : ∑ v ∈ S, -Real.log (v (4 : (P.curve x).F)) = d * Real.log 4 := by
    simpa only [Nat.cast_ofNat] using sum_neg_log_apply_natCast (n := 4) (by decide) hS4
  have hdyadic : ∑ v ∈ S, (if residueChar v = 2 then
      9 / 2 * |Real.log (v (genC' P x))| + 1 / 2 * |Real.log (v (genC' P x - 1))| +
        4 * -Real.log (v (4 : (P.curve x).F)) else 0) ≤ 5 * K.c * d + 4 * (d * Real.log 4) := by
    rw [← Finset.sum_filter]
    have hle : ∀ v ∈ S.filter (fun v => residueChar v = 2),
        9 / 2 * |Real.log (v (genC' P x))| + 1 / 2 * |Real.log (v (genC' P x - 1))| +
          4 * -Real.log (v (4 : (P.curve x).F)) ≤
        5 * K.c * localDeg (P.curve x).F v + 4 * -Real.log (v (4 : (P.curve x).F)) := by
      intro v hv
      obtain ⟨h₁, h₂⟩ := abs_log_two_le P x hx v (Finset.mem_filter.mp hv).2
      nlinarith only [h₁, h₂]
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hdeg : ∑ v ∈ S.filter (fun v => residueChar v = 2),
        (localDeg (P.curve x).F v : ℝ) ≤ d := by
      rw [← Nat.cast_sum]
      exact Nat.cast_le.mpr (sum_localDeg_filter_le S 2)
    have h4le : ∑ v ∈ S.filter (fun v => residueChar v = 2),
        -Real.log (v (4 : (P.curve x).F)) ≤ d * Real.log 4 := by
      rw [← hlog4]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun v _ _ => ?_
      exact neg_nonneg.mpr (Real.log_nonpos (apply_nonneg v _) (by
        simpa only [Nat.cast_ofNat] using apply_natCast_le_one v 4))
    exact add_le_add (mul_le_mul_of_nonneg_left hdeg (mul_nonneg (by norm_num)
      (CompactlyBounded.c_nonneg hx))) (mul_le_mul_of_nonneg_left h4le (by norm_num))
  have hlogℓ : ∑ v ∈ S, -Real.log (v (ℓ : (P.curve x).F)) = d * Real.log ℓ :=
    sum_neg_log_apply_natCast hℓ.ne_zero hSℓ
  rw [hgain, hlogℓ] at hfin
  have htotal := add_le_add hsum_arch hfin
  rw [hlogpf] at htotal
  apply le_of_mul_le_mul_left _ hd0
  nlinarith only [htotal, hdyadic]

end AbcAdaptation.Tripod.Cyclic
