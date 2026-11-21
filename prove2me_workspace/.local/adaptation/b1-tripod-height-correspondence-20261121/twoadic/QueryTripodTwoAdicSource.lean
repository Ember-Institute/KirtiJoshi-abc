/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Lean
import B1SourceReplay
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
Selected commands from revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
B1SourceReplay supplies the provider, Tate order, field identification, and
relative degree infrastructure. The field replays specialize the expected
CurveInputs field types using the original curve, arithmetic, Tate, and B assignments.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero

section ResidueChar

variable {k : Type*} [Field k] [NumberField k]

/-- `Iut.two_mem_maximalIdeal_iff` for an arbitrary prime `q`: `q ∈ 𝔭_v` iff the residue
characteristic of `v` is `q`. -/
lemma natCast_mem_maximalIdeal_iff (v : FinitePlace k) {q : ℕ} (hq : q.Prime) :
    (q : 𝓞 k) ∈ v.maximalIdeal.asIdeal ↔ residueChar v = q := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    CharP.cast_eq_zero_iff (𝓞 k ⧸ v.maximalIdeal.asIdeal) (ringChar _)]
  exact Nat.prime_dvd_prime_iff_eq (residueChar_prime v) hq

end ResidueChar

section MapEquiv

variable {k k' : Type*} [Field k] [NumberField k] [Field k'] [NumberField k']

variable (e : k ≃+* k') (v : FinitePlace k)

/-- The transported place has the same residue characteristic. -/
lemma FinitePlace.mapEquiv_residueChar :
    residueChar (FinitePlace.mapEquiv e v) = residueChar v := by
  rw [← natCast_mem_maximalIdeal_iff _ (residueChar_prime v), FinitePlace.mapEquiv_maximalIdeal,
    Ideal.mem_comap, map_natCast]
  exact (natCast_mem_maximalIdeal_iff v (residueChar_prime v)).mpr rfl

end MapEquiv

section LocalDeg

variable {K : Type*} [Field K] [NumberField K]

/-- `[K_w : ℚ_p] = e(𝔭_w/(p)) f(𝔭_w/(p))` for `p` the residue characteristic of `w`. -/
lemma localDeg_eq_ramificationIdx'_mul_inertiaDeg' (w : FinitePlace K) {q : ℕ}
    (hq : residueChar w = q) :
    localDeg K w = (Ideal.span {(q : ℤ)}).ramificationIdx' w.maximalIdeal.asIdeal *
      (Ideal.span {(q : ℤ)}).inertiaDeg' w.maximalIdeal.asIdeal := by
  subst hq
  rw [← under_int_eq]
  haveI : w.maximalIdeal.asIdeal.LiesOver (w.maximalIdeal.asIdeal.under ℤ) := inferInstance
  haveI : (w.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal w
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  unfold localDeg ramIdx inertDeg
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ w.maximalIdeal.asIdeal (under_int_ne_bot w),
    Ideal.inertiaDeg'_eq_inertiaDeg _ w.maximalIdeal.asIdeal]

/-- `∑_{w ∈ S, p_w = q} [K_w : ℚ_q] ≤ [K : ℚ]` for every finite set `S` of places of `K`
(from `∑_{w ∣ q} e_w f_w = [K : ℚ]`). -/
lemma sum_localDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), localDeg K w ≤ Module.finrank ℚ K := by
  classical
  by_cases hq : q.Prime
  · set p : Ideal ℤ := Ideal.span {(q : ℤ)} with hp
    haveI hmax : p.IsMaximal := by
      haveI hprime : p.IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
          (Nat.prime_iff_prime_int.1 hq)
      exact IsPrime.to_maximal_ideal (by
        rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero)
    have hp0 : p ≠ ⊥ := by
      rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq.ne_zero
    have hsum := Ideal.sum_ramification_inertia (𝓞 K) ℚ K hp0 (p := p)
    set T := S.filter (fun w => residueChar w = q) with hT
    have hover : ∀ w ∈ T, w.maximalIdeal.asIdeal.LiesOver p := by
      intro w hw
      rw [hT, Finset.mem_filter] at hw
      rw [hp, ← hw.2]
      exact liesOver_span_residueChar w
    have hsub : T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal) ⊆
        IsDedekindDomain.primesOverFinset p (𝓞 K) := by
      intro P hP
      rw [Finset.mem_image] at hP
      obtain ⟨w, hw, rfl⟩ := hP
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr
        ⟨inferInstance, hover w hw⟩
    have hinj : Set.InjOn (fun w : FinitePlace K => w.maximalIdeal.asIdeal) T := by
      intro w₁ _ w₂ _ h
      exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
    calc ∑ w ∈ T, localDeg K w
        = ∑ w ∈ T, p.ramificationIdx' w.maximalIdeal.asIdeal *
            p.inertiaDeg' w.maximalIdeal.asIdeal := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hT, Finset.mem_filter] at hw
          exact localDeg_eq_ramificationIdx'_mul_inertiaDeg' w hw.2
      _ = ∑ P ∈ T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          (Finset.sum_image (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hinj).symm
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 K),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          Finset.sum_le_sum_of_subset hsub
      _ = Module.finrank ℚ K := hsum
  · refine le_of_eq_of_le (Finset.sum_eq_zero ?_) (Nat.zero_le _)
    intro w hw
    rw [Finset.mem_filter] at hw
    exact absurd (hw.2 ▸ residueChar_prime w) hq

end LocalDeg

section LegendreValuation

open WeierstrassCurve Iut.Tripod

variable {K : Type*} [Field K] [NeZero (2 : K)] (v : Valuation K ℤᵐ⁰) {l : K}
  [(legendre l).IsElliptic]

/-- The nonvanishing of the factors of `j(E_λ)`, from `v(j) ≠ 0`. -/
lemma valuation_legendre_ne_zero (hj : v (legendre l).j ≠ 0) :
    v 256 ≠ 0 ∧ v (l ^ 2 - l + 1) ≠ 0 ∧ v l ≠ 0 ∧ v (l - 1) ≠ 0 := by
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl1 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  rw [legendre_j, map_div₀, map_mul, map_pow] at hj
  have hnum := (div_ne_zero_iff.mp hj).1
  exact ⟨(mul_ne_zero_iff.mp hnum).1,
    (pow_ne_zero_iff (by norm_num)).mp (mul_ne_zero_iff.mp hnum).2,
    (Valuation.ne_zero_iff v).mpr hl0, (Valuation.ne_zero_iff v).mpr hl1⟩

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendre_j (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  obtain ⟨h256, hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  rw [legendre_j, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit [NeZero (2 : K)] [(legendre l).IsElliptic] in
/-- `log v(λ² − λ + 1) ≤ log v(λ) + log v(λ − 1)` or `≤ 0` (ultrametric inequality for
`λ² − λ + 1 = λ(λ − 1) + 1`). -/
lemma log_valuation_sq_sub_add_one_le (hc : v (l ^ 2 - l + 1) ≠ 0) (hl : v l ≠ 0)
    (hl1 : v (l - 1) ≠ 0) :
    log (v (l ^ 2 - l + 1)) ≤ log (v l) + log (v (l - 1)) ∨ log (v (l ^ 2 - l + 1)) ≤ 0 := by
  have h : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rw [h] at hc ⊢
  rcases Valuation.map_add' v (l * (l - 1)) 1 with h1 | h1
  · left
    rw [map_mul] at h1
    rw [← log_mul hl hl1]
    exact (log_le_log hc (mul_ne_zero hl hl1)).mpr h1
  · right
    rw [map_one] at h1
    have := (log_le_log hc one_ne_zero).mpr h1
    simpa using this

/-- **The bound on `log v(j(E_λ))`**: if `v(256) ≤ 1` then
`log v(j) ≤ 2|log v(λ)| + 2|log v(λ − 1)|`. -/
lemma log_valuation_legendre_j_le (h256 : v 256 ≤ 1) (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) ≤ 2 * |log (v l)| + 2 * |log (v (l - 1))| := by
  obtain ⟨h256', hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendre_j v hj]
  have ha := le_abs_self (log (v l))
  have ha' := neg_abs_le (log (v l))
  have hb := le_abs_self (log (v (l - 1)))
  have hb' := neg_abs_le (log (v (l - 1)))
  have ha0 := abs_nonneg (log (v l))
  have hb0 := abs_nonneg (log (v (l - 1)))
  rcases log_valuation_sq_sub_add_one_le v hc hvl hvl1 with h | h
  · linarith
  · linarith

end LegendreValuation

end Iut

namespace Iut.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero

/-! ### The tripodal field `F_tpd = ℚ(λ) ⊆ F_λ` and its identification with `ℚ(λ) ⊆ ℚ̄` -/

variable (P : CurveProviders) (x : Pt)

theorem genT_ne_zero : genT P x ≠ 0 := fun h => gen'_ne_zero x.2.1 (congrArg Subtype.val h)

theorem genT_sub_one_ne_zero : genT P x - 1 ≠ 0 := by
  intro h
  exact gen'_ne_one x.2.2 (congrArg Subtype.val (sub_eq_zero.mp h))


theorem tpdEquiv_symm_gen : (tpdEquiv P x).symm (gen x.1) = genT P x := by
  rw [← tpdEquiv_genT, AlgEquiv.symm_apply_apply]

/-- The place of `ℚ(λ) ⊆ ℚ̄` corresponding to a place of `F_tpd`. -/
noncomputable abbrev tpdPlace (𝔭 : FinitePlace (tpd P x)) : FinitePlace (fieldOf x.1) :=
  FinitePlace.mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1) 𝔭

theorem tpdPlace_gen (𝔭 : FinitePlace (tpd P x)) : tpdPlace P x 𝔭 (gen x.1) = 𝔭 (genT P x) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply]
  congr 1
  exact tpdEquiv_symm_gen P x

theorem tpdPlace_gen_sub_one (𝔭 : FinitePlace (tpd P x)) :
    tpdPlace P x 𝔭 (gen x.1 - 1) = 𝔭 (genT P x - 1) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply, map_sub, map_one]
  congr 2
  exact tpdEquiv_symm_gen P x

theorem residueChar_tpdPlace (𝔭 : FinitePlace (tpd P x)) :
    residueChar (tpdPlace P x 𝔭) = residueChar 𝔭 :=
  FinitePlace.mapEquiv_residueChar _ _

/-- A compactly bounded subset has a nonnegative bound as soon as it is nonempty. -/
theorem CompactlyBounded.c_nonneg {K : CompactlyBounded} {x : Pt} (hx : x ∈ K.set) : 0 ≤ K.c := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace (fieldOf x.1)) := inferInstance
  exact (abs_nonneg _).trans (hx.2 w).1

/-- **The bound of a compactly bounded subset at a place of `F_tpd`**: for `𝔭` of residue
characteristic in `V`, `|ord_𝔭(λ)|·f_𝔭·log p ≤ c` and `|ord_𝔭(λ − 1)|·f_𝔭·log p ≤ c`. -/
theorem abs_log_valuation_mul_le {K : CompactlyBounded} (hx : x ∈ K.set)
    (𝔭 : FinitePlace (tpd P x)) (h𝔭 : residueChar 𝔭 ∈ K.V) :
    |((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (residueChar 𝔭)) ≤ K.c ∧
      |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (residueChar 𝔭)) ≤ K.c := by
  have hb := hx.1 (tpdPlace P x 𝔭) (by rwa [residueChar_tpdPlace])
  rw [tpdPlace_gen, tpdPlace_gen_sub_one, log_apply_eq _ (genT_ne_zero P x),
    log_apply_eq _ (genT_sub_one_ne_zero P x)] at hb
  have hpos : 0 ≤ (inertDeg (tpd P x) 𝔭 : ℝ) * Real.log (residueChar 𝔭) :=
    mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)
  obtain ⟨h1, h2⟩ := hb
  rw [abs_mul, abs_of_nonneg hpos] at h1 h2
  exact ⟨h1, h2⟩

/-! ### The `2`-adic bound -/

/-- `v_w(256) ≤ 1` at every finite place. -/
theorem valuation_256_le_one {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) :
    w.maximalIdeal.valuation T 256 ≤ 1 := by
  have : (256 : T) = algebraMap (𝓞 T) T 256 := by rw [map_ofNat]
  rw [this]
  exact valuation_le_one _ _

/-- The real-number bookkeeping of `term_le`. -/
lemma term_le_aux {N A B E Fr Fp L D c : ℝ} (hN : N ≤ 2 * E * (A + B))
    (hA : A * (Fp * L) ≤ c) (hB : B * (Fp * L) ≤ c) (hE : 0 ≤ E) (hFr : 0 ≤ Fr) (hFp : 0 ≤ Fp)
    (hL : 0 ≤ L) (hD : 1 ≤ D) (hc : 0 ≤ c) :
    N * (Fp * Fr) * L ≤ 4 * c * (D * (E * Fr)) := by
  calc N * (Fp * Fr) * L = N * (Fr * (Fp * L)) := by ring
    _ ≤ 2 * E * (A + B) * (Fr * (Fp * L)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
    _ = 2 * E * Fr * (A * (Fp * L) + B * (Fp * L)) := by ring
    _ ≤ 2 * E * Fr * (c + c) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = 4 * c * (1 * (E * Fr)) := by ring
    _ ≤ 4 * c * (D * (E * Fr)) := by gcongr

/-- **The local bound at a place over `2`**: for `w ∣ 𝔭` with `w` multiplicative and
`p_𝔭 = 2 ∈ V`, `h_w f_w log 2 ≤ 4c·[F_w : ℚ_2]`. -/
theorem term_le {K : CompactlyBounded} (hx : x ∈ K.set) {w : FinitePlace (P.curve x).F}
    (hw : w ∈ (P.curve x).badAll) (hw2 : residueChar w = 2) :
    ((P.tate x).qOrder w hw : ℝ) * inertDeg (P.curve x).F w * Real.log (residueChar w) ≤
      4 * K.c * localDeg (P.curve x).F w := by
  set 𝔭 : FinitePlace (tpd P x) := placeUnder w with h𝔭
  have hw𝔭 : FinitePlace.LiesOver w 𝔭 := liesOver_placeUnder w
  have h𝔭2 : residueChar 𝔭 = 2 := by rw [← residueChar_eq_of_liesOver hw𝔭, hw2]
  have hc := CompactlyBounded.c_nonneg hx
  -- the order of the Tate parameter is `log v_w(j)`
  have hvj := (P.curve x).valuation_j_eq_exp_qOrder hw
  have hj0 : w.maximalIdeal.valuation _ (P.curve x).E.j ≠ 0 := by rw [hvj]; exact exp_ne_zero
  have hn : ((P.tate x).qOrder w hw : ℤ) ≤
      2 * |log (w.maximalIdeal.valuation _ (genC' P x))| +
        2 * |log (w.maximalIdeal.valuation _ (genC' P x - 1))| := by
    have this : log (w.maximalIdeal.valuation _ (P.curve x).E.j) ≤
        2 * |log (w.maximalIdeal.valuation _ (genC' P x))| +
          2 * |log (w.maximalIdeal.valuation _ (genC' P x - 1))| :=
      log_valuation_legendre_j_le (w.maximalIdeal.valuation (P.curve x).F)
        (l := genC' P x) (valuation_256_le_one w) hj0
    rwa [hvj, log_exp] at this
  -- the valuations at `w` are the `e(w/𝔭)`-th powers of those at `𝔭`
  set e : ℕ := relRamIdx w 𝔭 with he
  have ha : log (w.maximalIdeal.valuation _ (genC' P x)) =
      e * log (𝔭.maximalIdeal.valuation _ (genT P x)) := by
    rw [← algebraMap_genT, valuation_algebraMap_eq_pow hw𝔭, log_pow, nsmul_eq_mul]
  have hb : log (w.maximalIdeal.valuation _ (genC' P x - 1)) =
      e * log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) := by
    rw [← algebraMap_genT, ← map_one (algebraMap (tpd P x) (P.curve x).F), ← map_sub,
      valuation_algebraMap_eq_pow hw𝔭, log_pow, nsmul_eq_mul]
  rw [ha, hb, abs_mul, abs_mul, Nat.abs_cast] at hn
  -- the bound of the compactly bounded subset at `𝔭`
  obtain ⟨hA, hB⟩ := abs_log_valuation_mul_le P x hx 𝔭 (by rw [h𝔭2]; exact K.two_mem)
  rw [h𝔭2] at hA hB
  -- the residue degrees and local degrees
  have hf : (inertDeg (P.curve x).F w : ℝ) = inertDeg (tpd P x) 𝔭 * relInertDeg w 𝔭 := by
    rw [inertDeg_eq_mul hw𝔭]; push_cast; ring
  have hd : (localDeg (P.curve x).F w : ℝ) = localDeg (tpd P x) 𝔭 * (e * relInertDeg w 𝔭) := by
    rw [localDeg_eq_mul hw𝔭]; push_cast; ring
  have hD : (1 : ℝ) ≤ localDeg (tpd P x) 𝔭 := by
    exact_mod_cast Nat.mul_pos (ramIdx_pos' 𝔭) (inertDeg_pos' 𝔭)
  have hn' : ((P.tate x).qOrder w hw : ℝ) ≤ 2 * e *
      (|((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| +
        |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)|) := by
    have h := (Int.cast_le (R := ℝ)).mpr hn
    push_cast at h
    linarith
  rw [hw2, hf, hd]
  exact term_le_aux hn' hA hB (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (log_natCast_nonneg _) hD hc

section

variable (K : CompactlyBounded)

/-- **The `2`-adic bound**: the contribution of the places over `2` to `log(q_∀(E_λ))` is
bounded by `B` on a compactly bounded subset (the places of `F_λ` over `2` lie over the
places of `ℚ(λ)` over `2 ∈ V`, where `|log|λ|_v|`, `|log|λ − 1|_v|` are bounded, and
`ord_w(q_w) = −ord_w(j(E_λ))` with `j = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`). -/
def TwoAdicBoundHyp (B : ℝ) : Prop := ∀ x ∈ K.set, (P.localData x).heightEq 2 ≤ B

end

/-- **The `2`-adic bound** `TwoAdicBoundHyp P K (4c)`: on a compactly bounded subset with
bound `c`, the contribution of the places over `2` to `log(q_∀(E_λ))` is at most `4c`. -/
theorem twoAdicBound' (K : CompactlyBounded) : TwoAdicBoundHyp P K (4 * K.c) := by
  intro x hx
  classical
  have hc := CompactlyBounded.c_nonneg hx
  change (∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
      (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
        (inertDeg (P.curve x).F w : ℝ) * Real.log (residueChar w))) /
      (Module.finrank ℚ (P.curve x).F : ℝ) ≤ 4 * K.c
  rw [div_le_iff₀ (by exact_mod_cast Module.finrank_pos)]
  calc ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
        (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
          (inertDeg (P.curve x).F w : ℝ) * Real.log (residueChar w))
      ≤ ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
          4 * K.c * (localDeg (P.curve x).F w : ℝ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hw
        split_ifs with h
        · exact term_le P x hx h hw.2
        · exact absurd hw.1 h
    _ = 4 * K.c * ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
          (localDeg (P.curve x).F w : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 * K.c * (Module.finrank ℚ (P.curve x).F : ℝ) := by
        gcongr
        let S : Finset (FinitePlace (P.curve x).F) := (P.arith x).badAll_finite.toFinset
        have hcast : ((∑ w ∈ S.filter (fun w => residueChar w = 2),
            localDeg (P.curve x).F w : ℕ) : ℝ) ≤ (Module.finrank ℚ (P.curve x).F : ℝ) :=
          Nat.cast_le.mpr (sum_localDeg_filter_le S 2)
        exact (Nat.cast_sum (R := ℝ) (S.filter fun w => residueChar w = 2)
          (localDeg (P.curve x).F)).symm.trans_le hcast

/-- **The `2`-adic bound** in the form `TwoAdicBoundHyp P K (max (4c) 0)`, with a nonnegative
bound. -/
theorem twoAdicBound (K : CompactlyBounded) : TwoAdicBoundHyp P K (max (4 * K.c) 0) :=
  fun x hx => (twoAdicBound' P K x hx).trans (le_max_left _ _)


/-- CurveFacts.lean:511 with the constant assigned at line 510. -/
theorem curveInputsBNonnegFieldReplay (K : CompactlyBounded) : 0 ≤ max (4 * K.c) 0 :=
  le_max_right _ _

/-- CurveFacts.lean:512 with the original constructor hypothesis retained. -/
theorem curveInputsHeightEqTwoFieldReplay (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0))
    (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    ((P.curve x).localHeightData (P.arith x) (P.tate x)).heightEq 2 ≤ max (4 * K.c) 0 :=
  hB x hx.1

/-- The same field after supplying the source theorem at the application of the constructor. -/
theorem curveInputsHeightEqTwoSpecializedReplay (P : CurveProviders) (K : CompactlyBounded)
    (d : ℕ) (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    ((P.curve x).localHeightData (P.arith x) (P.tate x)).heightEq 2 ≤ max (4 * K.c) 0 :=
  let hB := twoAdicBound P K
  hB x hx.1

end Iut.Tripod

namespace TripodTwoAdicSourceExpressions

open Lean Elab Term Meta

partial def encodeName : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[(encodeName p), Json.str "str", Json.str s]
  | .num p n => Json.arr #[(encodeName p), Json.str "num", toJson n]

def node (kind : String) (values : List (String × Json)) : Json :=
  Json.mkObj (("kind", Json.str kind) :: values)

partial def encodeLevel : Level → Except String Json
  | .zero => return node "zero" []
  | .succ u => return node "succ" [("arg", ← encodeLevel u)]
  | .max u v => return node "max" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .imax u v => return node "imax" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .param n => return node "param" [("name", encodeName n)]
  | .mvar _ => throw "Universe metavariable in compiler type"

def encodeBinder : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def encodeExpr : Expr → Except String Json
  | .bvar i => return node "bvar" [("index", toJson i)]
  | .sort u => return node "sort" [("level", ← encodeLevel u)]
  | .const n us => return node "const" [("name", encodeName n),
      ("levels", Json.arr (← us.toArray.mapM encodeLevel))]
  | .app f a => return node "app" [("fn", ← encodeExpr f), ("arg", ← encodeExpr a)]
  | .lam n t b bi => return node "lam" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .forallE n t b bi => return node "forall" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .letE n t v b nd => return node "let" [("name", encodeName n),
      ("type", ← encodeExpr t), ("value", ← encodeExpr v), ("body", ← encodeExpr b),
      ("nondependent", toJson nd)]
  | .lit (.natVal n) => return node "nat" [("value", toJson n)]
  | .lit (.strVal s) => return node "string" [("value", toJson s)]
  | .mdata _ b => encodeExpr b
  | .proj n i b => return node "proj" [("name", encodeName n), ("index", toJson i),
      ("body", ← encodeExpr b)]
  | .fvar _ => throw "Free variable in compiler declaration type"
  | .mvar _ => throw "Expression metavariable in compiler declaration type"

def checked {α : Type} (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "{e}"

def jsonFile (p : String) : MetaM Json := do
  checked (Json.parse (← IO.FS.readFile p))

def absoluteEnv (key : String) : MetaM String := do
  let some p ← IO.getEnv key | throwError "Missing environment variable {key}"
  unless p.startsWith "/" do throwError "Expected absolute path: {key}"
  return p

def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def ensureStandard (label : String) (axs : Array Name) : MetaM Unit := do
  for ax in axs do
    unless standardAxioms.contains ax do throwError "Unexpected axiom in {label}: {ax}"

abbrev AxiomCache := IO.Ref (Std.HashMap Name (Array Name))

-- The imported source environment is stable throughout this one export run.
-- Cache only successful collectAxioms results; errors still propagate normally.
def cachedAxioms (cache : AxiomCache) (name : Name) : MetaM (Array Name) := do
  if let some axs := (← cache.get)[name]? then return axs
  let axs ← collectAxioms name
  cache.modify fun entries => entries.insert name axs
  return axs

def expressionAxioms (cache : AxiomCache) (e : Expr) : MetaM (Array Name) := do
  let mut axs : Array Name := #[]
  for name in e.getUsedConstants do
    for ax in ← cachedAxioms cache name do
      unless axs.contains ax do axs := axs.push ax
  return axs.qsort Name.lt

partial def binderInventory : Expr → Array String
  | .forallE _ t b bi => #["forall:" ++ encodeBinder bi] ++ binderInventory t ++ binderInventory b
  | .lam _ t b bi => #["lambda:" ++ encodeBinder bi] ++ binderInventory t ++ binderInventory b
  | .app f a => binderInventory f ++ binderInventory a
  | .letE _ t v b _ => binderInventory t ++ binderInventory v ++ binderInventory b
  | .mdata _ e => binderInventory e
  | .proj _ _ e => binderInventory e
  | _ => #[]

def kind (ci : ConstantInfo) : String := match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def telescopeJson (type : Expr) : MetaM Json :=
  forallTelescope type fun xs result => do
    let binders ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      return Json.mkObj [("name", toJson d.userName.toString),
        ("binderInfo", toJson (encodeBinder d.binderInfo)),
        ("typeDisplay", toJson (← ppExpr d.type).pretty)]
    return Json.mkObj [("binders", Json.arr binders),
      ("resultDisplay", toJson (← ppExpr result).pretty)]

def requireClosed (label : String) (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then throwError "Open actual Expr {label}"

def checkedValueType (label : String) (value type : Expr) : MetaM Expr := do
  requireClosed label value
  requireClosed s!"TYPE of {label}" type
  let inferred ← match Kernel.check (← getEnv) {} value with
    | .ok t => pure t
    | .error ex => throwKernelException ex
  match Kernel.isDefEq (← getEnv) {} inferred type with
  | .ok true => pure ()
  | .ok false => throwError "Kernel actual value/TYPE mismatch {label}"
  | .error ex => throwKernelException ex
  return inferred

def fact (cache : AxiomCache) (name : Name) (expectedKind file : String)
    (line : Nat) (provenance : String) : MetaM Json := do
  let env ← getEnv
  let ci ← getConstInfo name
  unless kind ci == expectedKind do throwError "Unexpected declaration kind: {name}"
  let value ← match ci with
    | .defnInfo info => pure info.value
    | .thmInfo info => pure info.value
    | _ => throwError "Expected a definition or theorem: {name}"
  unless ci.levelParams.isEmpty do throwError "Unexpected universe parameter: {name}"
  if (env.getModuleIdxFor? name).isSome then throwError "Expected a declaration in the replay file: {name}"
  let type ← checkedValueType name.toString value ci.type
  let axs ← cachedAxioms cache name
  let typeAxs ← expressionAxioms cache ci.type
  let valueAxs ← expressionAxioms cache value
  for xs in #[axs, typeAxs, valueAxs] do ensureStandard name.toString xs
  let names := fun ns : Array Name => Json.arr (ns.qsort Name.lt |>.map encodeName)
  let axiomStrings := fun ns : Array Name => toJson (ns.qsort Name.lt |>.map Name.toString)
  return Json.mkObj [
    ("record", toJson "fullActualFact"),
    ("name", toJson name.toString), ("nameExpr", encodeName name),
    ("owner", toJson env.mainModule.toString), ("ownerNameExpr", encodeName env.mainModule),
    ("kind", toJson (kind ci)), ("levelParams", names ci.levelParams.toArray),
    ("actualTypeExpr", ← checked (encodeExpr ci.type)),
    ("actualValueExpr", ← checked (encodeExpr value)),
    ("valueRead", toJson true), ("isProposition", toJson (← isProp ci.type)),
    ("binderInventory", toJson (binderInventory ci.type)), ("telescope", ← telescopeJson ci.type),
    ("directTypeConstants", names ci.type.getUsedConstants),
    ("directValueConstants", names value.getUsedConstants),
    ("kernelInferredValueTypeExpr", ← checked (encodeExpr type)),
    ("kernelValueTypeMatchesActualTYPE", toJson true),
    ("axioms", axiomStrings axs), ("typeAxioms", axiomStrings typeAxs),
    ("valueAxioms", axiomStrings valueAxs), ("hasSorryAx", toJson (axs.contains `sorryAx)),
    ("referenceFile", toJson file),
    ("referenceLine", toJson line), ("provenance", toJson provenance)]

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do throwError "Expected Lean 4.35.0-rc3"
  let config ← jsonFile (← absoluteEnv "TRIPOD_TWOADIC_SOURCE_CONFIG")
  unless (← checked (config.getObjValAs? String "schema")) == "tripod-twoadic-source/v1" do
    throwError "Unexpected source export configuration"
  let output ← checked (config.getObjValAs? String "sourceFactsFile")
  unless output.startsWith "/" do throwError "Expected an absolute source facts file path"
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let twoadic := "Iut/Tripod/TwoAdic.lean"
  let curveFacts := "Iut/Tripod/CurveFacts.lean"
  let mut records : Array Json := #[]
  records := records.push (← fact cache ``Iut.Tripod.TwoAdicBoundHyp "definition" curveFacts 409
    "verbatim-source-definition-replay")
  records := records.push (← fact cache ``Iut.Tripod.twoAdicBound' "theorem" twoadic 568
    "source-theorem-replay-explicit-nat-sum-cast")
  records := records.push (← fact cache ``Iut.Tripod.twoAdicBound "theorem" twoadic 595
    "verbatim-source-theorem-replay")
  records := records.push (← fact cache ``Iut.Tripod.curveInputsBNonnegFieldReplay "theorem"
    curveFacts 511 "source-constructor-field-rhs-replay")
  records := records.push (← fact cache ``Iut.Tripod.curveInputsHeightEqTwoFieldReplay "theorem"
    curveFacts 512 "source-constructor-field-rhs-replay")
  records := records.push (← fact cache ``Iut.Tripod.curveInputsHeightEqTwoSpecializedReplay "theorem"
    curveFacts 512 "source-constructor-field-rhs-specialized-with-twoAdicBound")
  IO.FS.writeFile output (String.intercalate "\n" (records.toList.map Json.compress) ++ "\n")
  logInfo m!"Exported {records.size} source declarations with kernel and axiom checks"

end TripodTwoAdicSourceExpressions
