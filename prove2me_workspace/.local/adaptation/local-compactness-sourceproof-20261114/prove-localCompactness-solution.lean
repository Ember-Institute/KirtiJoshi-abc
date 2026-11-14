import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FermatLocalBelyi
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.LinearAlgebra.Countable

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source.Local

open Filter Topology Polynomial

/-- **Infinite pigeonhole**: a sequence with values in a finite type is constant along a
subsequence. -/
theorem exists_strictMono_eq {α : Type*} [Finite α] (f : ℕ → α) :
    ∃ (c : α) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ n, f (φ n) = c := by
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber f
  have hinf : (setOf fun n => f n = c).Infinite := Set.infinite_coe_iff.mp hc
  exact ⟨c, Nat.nth (fun n => f n = c), Nat.nth_strictMono hinf,
    fun n => Nat.nth_mem_of_infinite hinf n⟩

/-- A subsequence of the terms satisfying a predicate that holds infinitely often. -/
theorem exists_strictMono_forall_of_infinite {P : ℕ → Prop} (h : (setOf P).Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) :=
  ⟨Nat.nth P, Nat.nth_strictMono h, fun n => Nat.nth_mem_of_infinite h n⟩

/-- Pigeonhole for a sequence of natural numbers bounded by `d`. -/
theorem exists_strictMono_eq_of_le {f : ℕ → ℕ} {d : ℕ} (hf : ∀ n, f n ≤ d) :
    ∃ (c : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ n, f (φ n) = c := by
  obtain ⟨c, φ, hφ, hc⟩ := exists_strictMono_eq (fun n => (⟨f n, Nat.lt_succ_of_le (hf n)⟩ :
    Fin (d + 1)))
  exact ⟨c, φ, hφ, fun n => congrArg Fin.val (hc n)⟩

/-- If `t n ^ c ≤ ε n` with `t n ≥ 0`, `c ≠ 0` and `ε n → 0`, then `t n → 0`. -/
theorem tendsto_zero_of_pow_le {t ε : ℕ → ℝ} {c : ℕ} (hc : c ≠ 0) (ht : ∀ n, 0 ≤ t n)
    (hle : ∀ n, t n ^ c ≤ ε n) (hε : Tendsto ε atTop (𝓝 0)) : Tendsto t atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hε ⊢
  intro δ hδ
  obtain ⟨N, hN⟩ := hε (δ ^ c) (pow_pos hδ c)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ht n)]
  by_contra h2
  push Not at h2
  have : δ ^ c ≤ t n ^ c := pow_le_pow_left₀ hδ.le h2 c
  have h3 : ε n < δ ^ c := lt_of_abs_lt h1
  linarith [hle n]

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- The norm of `ℚ̄_p` is the spectral norm. -/
theorem PadicAlgCl.norm_eq_spectralNorm (x : PadicAlgCl p) :
    ‖x‖ = spectralNorm ℚ_[p] (PadicAlgCl p) x := rfl

/-- If `‖x‖ ≤ 1` in `ℚ̄_p`, the coefficients of the minimal polynomial of `x` over `ℚ_p`
are `p`-adic integers. -/
theorem PadicAlgCl.norm_coeff_minpoly_le_one {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (i : ℕ) :
    ‖(minpoly ℚ_[p] x).coeff i‖ ≤ 1 := by
  have hint : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  rw [PadicAlgCl.norm_eq_spectralNorm, spectralNorm] at hx
  exact (spectralValue_le_one_iff (minpoly.monic hint)).mp hx i

/-- A monic polynomial written with its coefficients. -/
theorem monic_eq_sum {R : Type*} [CommRing R] {P : R[X]} (hP : P.Monic) :
    P = X ^ P.natDegree + ∑ i : Fin P.natDegree, C (P.coeff i) * X ^ (i : ℕ) := by
  conv_lhs => rw [hP.as_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i)]

/-- The inverse of an element has the same degree. -/
theorem natDegree_minpoly_inv {K L : Type*} [Field K] [Field L] [Algebra K L] (x : L) :
    (minpoly K x⁻¹).natDegree = (minpoly K x).natDegree := by
  by_cases hx : IsIntegral K x
  · by_cases h0 : x = 0
    · simp [h0]
    have hxi : IsIntegral K x⁻¹ := by
      have := (IsIntegral.isAlgebraic hx).inv
      exact this.isIntegral
    rw [← IntermediateField.adjoin.finrank hx, ← IntermediateField.adjoin.finrank hxi]
    have : IntermediateField.adjoin K {x⁻¹} = IntermediateField.adjoin K {x} := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have := inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
        rwa [inv_inv] at this
    rw [this]
  · have hxi : ¬ IsIntegral K x⁻¹ := fun h => by
      have := (IsIntegral.isAlgebraic h).inv
      rw [inv_inv] at this
      exact hx this.isIntegral
    rw [minpoly.eq_zero hx, minpoly.eq_zero hxi]

/-- In an algebraically closed normed field, a monic polynomial `G` of positive degree has a
root `r` with `‖x − r‖ ^ deg G ≤ ‖G(x)‖`. -/
theorem exists_mem_roots_norm_sub_pow_le {K : Type*} [NormedField K] [IsAlgClosed K]
    {G : K[X]} (hG : G.Monic) (hdeg : 0 < G.natDegree) (x : K) :
    ∃ r ∈ G.roots, ‖x - r‖ ^ G.natDegree ≤ ‖G.eval x‖ := by
  have hsplit : G = (G.roots.map fun r => X - C r).prod :=
    (IsAlgClosed.splits G).eq_prod_roots_of_monic hG
  have hcard : G.roots.card = G.natDegree :=
    (IsAlgClosed.splits G).natDegree_eq_card_roots.symm
  have hne : G.roots ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    omega
  obtain ⟨r, hr, hmin⟩ := Multiset.exists_min_image (fun r => ‖x - r‖) hne
  refine ⟨r, hr, ?_⟩
  have key : ∀ s : Multiset K, (∀ y ∈ s, ‖x - r‖ ≤ ‖x - y‖) →
      ‖x - r‖ ^ Multiset.card s ≤ ‖((s.map fun r => X - C r).prod).eval x‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul, Multiset.card_cons,
        pow_succ, mul_comm]
      simp only [eval_sub, eval_X, eval_C]
      exact mul_le_mul (hs a (Multiset.mem_cons_self a s))
        (ih fun y hy => hs y (Multiset.mem_cons_of_mem hy)) (by positivity) (norm_nonneg _)
  have := key G.roots hmin
  rwa [← hsplit, hcard] at this

/-- **The bounded case**: a sequence in the closed unit ball of `ℚ̄_p` whose terms have
degree at most `d` over `ℚ_p` has a convergent subsequence. -/
theorem PadicAlgCl.exists_tendsto_of_norm_le_one (d : ℕ) (a : ℕ → PadicAlgCl p)
    (hdeg : ∀ n, (minpoly ℚ_[p] (a n)).natDegree ≤ d) (hnorm : ∀ n, ‖a n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b, Tendsto (a ∘ φ) atTop (𝓝 b) := by
  classical
  have hint : ∀ x : PadicAlgCl p, IsIntegral ℚ_[p] x :=
    fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  -- constant degree along a subsequence
  obtain ⟨c, φ₁, hφ₁, hc⟩ := exists_strictMono_eq_of_le hdeg
  set a₁ := a ∘ φ₁ with ha₁
  have hc₁ : ∀ n, (minpoly ℚ_[p] (a₁ n)).natDegree = c := hc
  have hcpos : 0 < c := by
    rw [← hc₁ 0]
    exact minpoly.natDegree_pos (hint _)
  -- the coefficient vectors lie in the unit ball
  set v : ℕ → (Fin c → ℚ_[p]) := fun n i => (minpoly ℚ_[p] (a₁ n)).coeff i with hv
  have hvmem : ∀ n, v n ∈ Metric.closedBall (0 : Fin c → ℚ_[p]) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact fun i => PadicAlgCl.norm_coeff_minpoly_le_one (hnorm _) i
  obtain ⟨w, -, ψ, hψ, hw⟩ := (isCompact_closedBall (0 : Fin c → ℚ_[p]) 1).tendsto_subseq hvmem
  set a₂ := a₁ ∘ ψ with ha₂
  -- the limit polynomial
  set g : ℚ_[p][X] := X ^ c + ∑ i : Fin c, C (w i) * X ^ (i : ℕ) with hg
  -- `g(a₂ n) → 0`
  have hgeval : ∀ n, aeval (a₂ n) g =
      ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p) (w i - v (ψ n) i) * (a₂ n) ^ (i : ℕ) := by
    intro n
    have hmin : aeval (a₂ n) (minpoly ℚ_[p] (a₂ n)) = 0 := minpoly.aeval _ _
    have hm := monic_eq_sum (minpoly.monic (hint (a₂ n)))
    have hdn : (minpoly ℚ_[p] (a₂ n)).natDegree = c := hc₁ (ψ n)
    rw [hm] at hmin
    have hmin' : (a₂ n) ^ c + ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p)
        ((minpoly ℚ_[p] (a₂ n)).coeff i) * (a₂ n) ^ (i : ℕ) = 0 := by
      rw [map_add, map_pow, aeval_X, map_sum] at hmin
      simp only [map_mul, aeval_C, map_pow, aeval_X] at hmin
      convert hmin using 2
      · rw [hdn]
      · rw [hdn]
    rw [hg, map_add, map_pow, aeval_X, map_sum]
    simp only [map_mul, aeval_C, map_pow, aeval_X]
    have : ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p) (w i - v (ψ n) i) * a₂ n ^ (i : ℕ) =
        (a₂ n ^ c + ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p) (w i) * a₂ n ^ (i : ℕ)) -
        (a₂ n ^ c + ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p)
          ((minpoly ℚ_[p] (a₂ n)).coeff i) * a₂ n ^ (i : ℕ)) := by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, hv, ha₂, Function.comp_apply]
      ring
    rw [this, hmin', sub_zero]
  have hgto : Tendsto (fun n => ‖aeval (a₂ n) g‖) atTop (𝓝 0) := by
    have hbound : ∀ n, ‖aeval (a₂ n) g‖ ≤ ∑ i : Fin c, ‖w i - v (ψ n) i‖ := by
      intro n
      rw [hgeval n]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, norm_pow, norm_algebraMap']
      have h1 : ‖a₂ n‖ ^ (i : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hnorm _)
      calc ‖w i - v (ψ n) i‖ * ‖a₂ n‖ ^ (i : ℕ) ≤ ‖w i - v (ψ n) i‖ * 1 :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖w i - v (ψ n) i‖ := mul_one _
    have hsum : Tendsto (fun n => ∑ i : Fin c, ‖w i - v (ψ n) i‖) atTop (𝓝 0) := by
      have : (0 : ℝ) = ∑ i : Fin c, ‖w i - w i‖ := by simp
      rw [this]
      refine tendsto_finsetSum _ fun i _ => ?_
      exact ((continuous_apply i).tendsto w |>.comp hw).const_sub (w i) |>.norm
    exact squeeze_zero (fun n => norm_nonneg _) hbound hsum
  -- factor `g` over `ℚ̄_p` and find a nearby root
  have hgmonic : g.Monic := by
    rw [hg]
    refine monic_X_pow_add ?_
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i _
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast i.2
  have hgdeg : g.natDegree = c := by
    rw [hg, natDegree_add_eq_left_of_degree_lt]
    · simp
    · refine (degree_sum_le _ _).trans_lt ?_
      rw [degree_X_pow, Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro i _
      refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
      exact_mod_cast i.2
  set G := g.map (algebraMap ℚ_[p] (PadicAlgCl p)) with hG
  have hGmonic : G.Monic := hgmonic.map _
  have hGdeg : G.natDegree = c := by rw [hG, natDegree_map, hgdeg]
  have hGeval : ∀ n, G.eval (a₂ n) = aeval (a₂ n) g := fun n => by
    rw [hG, eval_map_algebraMap]
  have hnear : ∀ n, ∃ r ∈ G.roots, ‖a₂ n - r‖ ^ c ≤ ‖aeval (a₂ n) g‖ := by
    intro n
    rw [← hGeval n, ← hGdeg]
    exact exists_mem_roots_norm_sub_pow_le hGmonic (hGdeg ▸ hcpos) (a₂ n)
  choose r hrmem hr using hnear
  -- the roots form a finite set: pigeonhole
  set S : Finset (PadicAlgCl p) := G.roots.toFinset
  obtain ⟨r₀, χ, hχ, hr₀⟩ := exists_strictMono_eq (fun n => (⟨r n, by
    simpa [S] using hrmem n⟩ : S))
  refine ⟨φ₁ ∘ ψ ∘ χ, hφ₁.comp (hψ.comp hχ), r₀, ?_⟩
  have hdist : Tendsto (fun n => ‖a₂ (χ n) - r₀‖) atTop (𝓝 0) := by
    refine tendsto_zero_of_pow_le hcpos.ne' (fun n => norm_nonneg _) (fun n => ?_)
      (hgto.comp hχ.tendsto_atTop)
    have := hr (χ n)
    have hrr : r (χ n) = r₀ := congrArg Subtype.val (hr₀ n)
    rw [hrr] at this
    exact this
  have : Tendsto (fun n => a₂ (χ n)) atTop (𝓝 (r₀ : PadicAlgCl p)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hdist
  exact this

/-- **The dichotomy in `ℚ̄_p`**: a sequence in `ℚ̄_p = PadicAlgCl p` whose terms have degree
at most `d` over `ℚ_p` has a subsequence which converges or whose norm tends to `∞`. -/
theorem PadicAlgCl.exists_tendsto_or_tendsto_norm_atTop (d : ℕ) (a : ℕ → PadicAlgCl p)
    (hdeg : ∀ n, (minpoly ℚ_[p] (a n)).natDegree ≤ d) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop) := by
  by_cases h : (setOf fun n => ‖a n‖ ≤ 1).Infinite
  · obtain ⟨φ₁, hφ₁, h1⟩ := exists_strictMono_forall_of_infinite h
    obtain ⟨ψ, hψ, b, hb⟩ :=
      PadicAlgCl.exists_tendsto_of_norm_le_one d (a ∘ φ₁) (fun n => hdeg _) h1
    exact ⟨φ₁ ∘ ψ, hφ₁.comp hψ, Or.inl ⟨b, hb⟩⟩
  · rw [Set.not_infinite] at h
    obtain ⟨N, hN⟩ := h.bddAbove
    have hgt : ∀ n, 1 < ‖a (n + N + 1)‖ := by
      intro n
      by_contra hle
      push Not at hle
      have := hN hle
      omega
    have hne : ∀ n, a (n + N + 1) ≠ 0 := fun n h0 => by
      have := hgt n
      rw [h0, norm_zero] at this
      linarith
    set b : ℕ → PadicAlgCl p := fun n => (a (n + N + 1))⁻¹ with hb
    have hbdeg : ∀ n, (minpoly ℚ_[p] (b n)).natDegree ≤ d := by
      intro n
      rw [hb, natDegree_minpoly_inv]
      exact hdeg _
    have hbnorm : ∀ n, ‖b n‖ ≤ 1 := by
      intro n
      rw [hb, norm_inv]
      exact inv_le_one_of_one_le₀ (hgt n).le
    obtain ⟨ψ, hψ, β, hβ⟩ := PadicAlgCl.exists_tendsto_of_norm_le_one d b hbdeg hbnorm
    have hφ : StrictMono fun n => ψ n + N + 1 := fun m n hmn => by
      have := hψ hmn
      change ψ m + N + 1 < ψ n + N + 1
      omega
    refine ⟨fun n => ψ n + N + 1, hφ, ?_⟩
    by_cases hβ0 : β = 0
    · right
      have h0 : Tendsto (fun n => ‖b (ψ n)‖) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have := hβ.norm
          rwa [hβ0, norm_zero] at this
        · exact norm_pos_iff.mpr (inv_ne_zero (hne _))
      have := h0.inv_tendsto_nhdsGT_zero
      refine this.congr fun n => ?_
      simp [hb, norm_inv]
    · left
      refine ⟨β⁻¹, ?_⟩
      have := hβ.inv₀ hβ0
      refine this.congr fun n => ?_
      simp [hb]

end Padic

/-- **The dichotomy in a proper normed field** (e.g. `ℂ`): every sequence has a subsequence
which converges or whose norm tends to `∞`. -/
theorem exists_tendsto_or_tendsto_norm_atTop {K : Type*} [NormedField K] [ProperSpace K]
    (a : ℕ → K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop) := by
  by_cases h : ∃ C : ℝ, (setOf fun n => ‖a n‖ ≤ C).Infinite
  · obtain ⟨C, hC⟩ := h
    obtain ⟨φ₁, hφ₁, h1⟩ := exists_strictMono_forall_of_infinite hC
    have hmem : ∀ n, (a ∘ φ₁) n ∈ Metric.closedBall (0 : K) C := fun n => by
      rw [mem_closedBall_zero_iff]
      exact h1 n
    obtain ⟨b, -, ψ, hψ, hb⟩ := (isCompact_closedBall (0 : K) C).tendsto_subseq hmem
    exact ⟨φ₁ ∘ ψ, hφ₁.comp hψ, Or.inl ⟨b, hb⟩⟩
  · push Not at h
    refine ⟨id, strictMono_id, Or.inr ?_⟩
    rw [tendsto_atTop]
    intro C
    obtain ⟨N, hN⟩ := (h C).bddAbove
    refine eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hN (show n ∈ setOf fun n => ‖a n‖ ≤ C from hlt.le)
    omega

end AbcAdaptation.Tripod.Fermat.Proper.Source.Local

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source.Local


open Filter Topology

section Convergence

variable {E : Type*} [NormedField E]

/-- Convergence of a sequence of points of `ℙ¹(E) = Option E` (`none = ∞`). -/
def TendstoP1 (a : ℕ → Option E) : Option E → Prop
  | some β => ∀ ε > 0, ∀ᶠ n in atTop, ∃ α, a n = some α ∧ ‖α - β‖ < ε
  | none => ∀ R : ℝ, ∀ᶠ n in atTop, ∀ α, a n = some α → R < ‖α‖

theorem TendstoP1.comp_of_tendsto {a : ℕ → Option E} {b : Option E} (h : TendstoP1 a b)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) : TendstoP1 (a ∘ φ) b := by
  cases b with
  | none => exact fun R => hφ.eventually (h R)
  | some β => exact fun ε hε => hφ.eventually (h ε hε)

/-- Convergence only depends on the tail. -/
theorem TendstoP1.congr_eventually {a a' : ℕ → Option E} {b : Option E} (h : TendstoP1 a b)
    (h' : ∀ᶠ n in atTop, a n = a' n) : TendstoP1 a' b := by
  cases b with
  | none =>
    intro R
    filter_upwards [h R, h'] with n hn hn' α hα
    exact hn α (hn'.trans hα)
  | some β =>
    intro ε hε
    filter_upwards [h ε hε, h'] with n hn hn'
    obtain ⟨α, hα, hlt⟩ := hn
    exact ⟨α, hn' ▸ hα, hlt⟩

/-- Limits in `ℙ¹(E)` are unique. -/
theorem TendstoP1.unique {a : ℕ → Option E} {b b' : Option E} (h : TendstoP1 a b)
    (h' : TendstoP1 a b') : b = b' := by
  cases b with
  | none =>
    cases b' with
    | none => rfl
    | some β' =>
      exfalso
      obtain ⟨n, hn⟩ := ((h (‖β'‖ + 1)).and (h' 1 one_pos)).exists
      obtain ⟨α, hα, hlt⟩ := hn.2
      have h1 := hn.1 α hα
      have : ‖α‖ ≤ ‖β'‖ + ‖α - β'‖ := by
        calc ‖α‖ = ‖β' + (α - β')‖ := by rw [add_sub_cancel]
          _ ≤ ‖β'‖ + ‖α - β'‖ := norm_add_le _ _
      linarith
  | some β =>
    cases b' with
    | none =>
      exfalso
      obtain ⟨n, hn⟩ := ((h' (‖β‖ + 1)).and (h 1 one_pos)).exists
      obtain ⟨α, hα, hlt⟩ := hn.2
      have h1 := hn.1 α hα
      have : ‖α‖ ≤ ‖β‖ + ‖α - β‖ := by
        calc ‖α‖ = ‖β + (α - β)‖ := by rw [add_sub_cancel]
          _ ≤ ‖β‖ + ‖α - β‖ := norm_add_le _ _
      linarith
    | some β' =>
      congr 1
      by_contra hne
      have hd : 0 < ‖β - β'‖ / 2 := by
        have : 0 < ‖β - β'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        linarith
      obtain ⟨n, hn⟩ := ((h _ hd).and (h' _ hd)).exists
      obtain ⟨α, hα, hlt⟩ := hn.1
      obtain ⟨α', hα', hlt'⟩ := hn.2
      rw [hα] at hα'
      cases hα'
      have : ‖β - β'‖ ≤ ‖α - β‖ + ‖α - β'‖ := by
        calc ‖β - β'‖ = ‖(α - β') - (α - β)‖ := by congr 1; ring
          _ ≤ ‖α - β'‖ + ‖α - β‖ := norm_sub_le _ _
          _ = ‖α - β‖ + ‖α - β'‖ := add_comm _ _
      linarith

/-- Convergence to a finite value, in terms of `Tendsto`. -/
theorem tendstoP1_some_iff {a : ℕ → E} {β : E} :
    TendstoP1 (fun n => some (a n)) (some β) ↔ Tendsto a atTop (𝓝 β) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h ε hε)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨α, hα, hlt⟩ := hN n hn
    cases hα
    rwa [dist_eq_norm]
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact eventually_atTop.mpr ⟨N, fun n hn => ⟨a n, rfl, by rw [← dist_eq_norm]; exact hN n hn⟩⟩

/-- **Sequential compactness in `ℙ¹(E)`**, from the dichotomy "convergent or unbounded" for
the finite values in a class `Good`. -/
theorem exists_tendstoP1 {Good : E → Prop}
    (hcpt : ∀ a : ℕ → E, (∀ n, Good (a n)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop))
    (a : ℕ → Option E) (ha : ∀ n α, a n = some α → Good α) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b, TendstoP1 (a ∘ φ) b := by
  by_cases hinf : (setOf fun n => a n = none).Infinite
  · refine ⟨Nat.nth (fun n => a n = none), Nat.nth_strictMono hinf, none, fun R => ?_⟩
    exact Eventually.of_forall fun n α hα => by
      have : a (Nat.nth (fun n => a n = none) n) = none := Nat.nth_mem_of_infinite hinf n
      simp only [Function.comp] at hα
      rw [this] at hα
      cases hα
  · -- eventually all values are finite
    obtain ⟨N, hN⟩ := (Set.not_infinite.mp hinf).bddAbove
    have hsome : ∀ n, ∃ α, a (n + N + 1) = some α := by
      intro n
      cases h : a (n + N + 1) with
      | none =>
        have := hN (show n + N + 1 ∈ setOf fun n => a n = none from h)
        omega
      | some α => exact ⟨α, rfl⟩
    choose α hα using hsome
    obtain ⟨φ, hφ, hlim⟩ := hcpt α (fun n => ha _ _ (hα n))
    have hmono : StrictMono (fun n => φ n + N + 1) := fun m n hmn => by
      have := hφ hmn
      change φ m + N + 1 < φ n + N + 1
      omega
    refine ⟨fun n => φ n + N + 1, hmono, ?_⟩
    rcases hlim with ⟨b, hb⟩ | hinfty
    · refine ⟨some b, ?_⟩
      have : TendstoP1 (fun n => some (α (φ n))) (some b) := tendstoP1_some_iff.mpr hb
      refine this.congr_eventually (Eventually.of_forall fun n => ?_)
      simp [hα]
    · refine ⟨none, fun R => ?_⟩
      filter_upwards [hinfty.eventually_gt_atTop R] with n hn β hβ
      simp only [Function.comp, hα] at hβ
      cases hβ
      exact hn

end Convergence

section Diagonal

/-- A family of strictly monotone maps refining each other. -/
theorem exists_diagonal {P : ℕ → (ℕ → ℕ) → Prop}
    (hP : ∀ k (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P k (φ ∘ ψ))
    (hmono : ∀ k (φ : ℕ → ℕ) (ψ : ℕ → ℕ), P k φ → Tendsto ψ atTop atTop → P k (φ ∘ ψ)) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∀ k, ∃ χ : ℕ → ℕ, Tendsto χ atTop atTop ∧
      ∃ φ : ℕ → ℕ, P k φ ∧ ∀ n, k < n → D n = φ (χ n) := by
  classical
  -- the refining sequence
  let step : ℕ → {φ : ℕ → ℕ // StrictMono φ} → {φ : ℕ → ℕ // StrictMono φ} :=
    fun k φ => ⟨φ.1 ∘ (hP k φ.1 φ.2).choose, φ.2.comp (hP k φ.1 φ.2).choose_spec.1⟩
  let Φ : ℕ → {φ : ℕ → ℕ // StrictMono φ} := fun n =>
    Nat.rec ⟨id, strictMono_id⟩ (fun k φ => step k φ) n
  have hΦsucc : ∀ k, Φ (k + 1) = step k (Φ k) := fun k => rfl
  have hstepP : ∀ k, P k (Φ (k + 1)).1 := fun k => by
    rw [hΦsucc]
    exact (hP k (Φ k).1 (Φ k).2).choose_spec.2
  -- `Φ n = Φ k ∘ ρ` with `ρ` strictly monotone, for `k ≤ n`
  have hrefine : ∀ k n, k ≤ n → ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ (Φ n).1 = (Φ k).1 ∘ ρ := by
    intro k n hkn
    induction n, hkn using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ n hkn ih =>
      obtain ⟨ρ, hρ, hΦ⟩ := ih
      refine ⟨ρ ∘ (hP n (Φ n).1 (Φ n).2).choose, hρ.comp
        (hP n (Φ n).1 (Φ n).2).choose_spec.1, ?_⟩
      rw [hΦsucc]
      change (Φ n).1 ∘ _ = _
      funext m
      exact congrFun hΦ _
  set D : ℕ → ℕ := fun n => (Φ n).1 n with hD
  have hDmono : StrictMono D := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    obtain ⟨ρ, hρ, hΦ⟩ := hrefine n (n + 1) (Nat.le_succ n)
    change (Φ n).1 n < (Φ (n + 1)).1 (n + 1)
    rw [hΦ]
    exact (Φ n).2 (lt_of_lt_of_le (Nat.lt_succ_self n) (hρ.id_le (n + 1)))
  refine ⟨D, hDmono, fun k => ?_⟩
  -- along `D`, eventually a subsequence of `Φ (k+1)`
  choose ρ hρ hΦρ using fun n => (fun h => hrefine (k + 1) (max n (k + 1)) h)
    (le_max_right n (k + 1))
  refine ⟨fun n => ρ n (max n (k + 1)), ?_, (Φ (k + 1)).1, hstepP k, fun n hkn => ?_⟩
  · refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    exact (le_max_left n (k + 1)).trans ((hρ n).id_le _)
  · change (Φ n).1 n = (Φ (k + 1)).1 (ρ n (max n (k + 1)))
    have hn : k + 1 ≤ n := hkn
    have := congrFun (hΦρ n) n
    simp only [Function.comp] at this
    rw [max_eq_left hn] at this ⊢
    exact this

end Diagonal

end AbcAdaptation.Tripod.Fermat.Proper.Source.Local

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source.Local

open Filter Topology

section EPlace

variable {K : Type*} [Field K] {E : Type*} [NormedField E]

/-- An `E`-valued place of `K`: a valuation subring with a ring homomorphism to `E` whose
kernel is the maximal ideal. -/
structure EPlace (K E : Type*) [Field K] [NormedField E] where
  /-- The valuation subring. -/
  O : ValuationSubring K
  /-- The evaluation map. -/
  ψ : O →+* E
  /-- The kernel of `ψ` consists of the nonunits. -/
  eq_zero_iff : ∀ f : O, ψ f = 0 ↔ ¬ IsUnit f

namespace EPlace

open Classical in
/-- The value `f(x) ∈ ℙ¹(E)` of `f ∈ K` at an `E`-valued place (`none = ∞`). -/
noncomputable def val (x : EPlace K E) (f : K) : Option E :=
  if h : f ∈ x.O then some (x.ψ ⟨f, h⟩) else none

theorem val_of_mem (x : EPlace K E) {f : K} (h : f ∈ x.O) : x.val f = some (x.ψ ⟨f, h⟩) := by
  simp [val, h]

theorem val_of_notMem (x : EPlace K E) {f : K} (h : f ∉ x.O) : x.val f = none := by
  simp [val, h]

theorem val_eq_some_iff (x : EPlace K E) {f : K} {α : E} :
    x.val f = some α ↔ ∃ h : f ∈ x.O, x.ψ ⟨f, h⟩ = α := by
  by_cases h : f ∈ x.O
  · simp [val, h]
  · simp [val, h]

theorem val_add (x : EPlace K E) {f g : K} {α β : E} (hf : x.val f = some α)
    (hg : x.val g = some β) : x.val (f + g) = some (α + β) := by
  obtain ⟨hf', rfl⟩ := (val_eq_some_iff x).mp hf
  obtain ⟨hg', rfl⟩ := (val_eq_some_iff x).mp hg
  rw [val_of_mem x (add_mem hf' hg')]
  congr 1
  rw [← map_add]
  rfl

theorem val_mul (x : EPlace K E) {f g : K} {α β : E} (hf : x.val f = some α)
    (hg : x.val g = some β) : x.val (f * g) = some (α * β) := by
  obtain ⟨hf', rfl⟩ := (val_eq_some_iff x).mp hf
  obtain ⟨hg', rfl⟩ := (val_eq_some_iff x).mp hg
  rw [val_of_mem x (mul_mem hf' hg')]
  congr 1
  rw [← map_mul]
  rfl

theorem val_neg (x : EPlace K E) {f : K} {α : E} (hf : x.val f = some α) :
    x.val (-f) = some (-α) := by
  obtain ⟨hf', rfl⟩ := (val_eq_some_iff x).mp hf
  rw [val_of_mem x (neg_mem hf')]
  congr 1
  rw [← map_neg]
  rfl

theorem val_one (x : EPlace K E) : x.val 1 = some 1 := by
  rw [val_of_mem x (one_mem _)]
  congr 1
  exact map_one x.ψ

theorem val_zero (x : EPlace K E) : x.val 0 = some 0 := by
  rw [val_of_mem x (zero_mem _)]
  congr 1
  exact map_zero x.ψ

/-- Inversion: if `f(x) = α ≠ 0` then `f⁻¹(x) = α⁻¹`. -/
theorem val_inv_of_ne_zero (x : EPlace K E) {f : K} {α : E} (hf : x.val f = some α)
    (hα : α ≠ 0) : x.val f⁻¹ = some α⁻¹ := by
  obtain ⟨hf', rfl⟩ := (val_eq_some_iff x).mp hf
  have hunit : IsUnit (⟨f, hf'⟩ : x.O) := by
    by_contra h
    exact hα ((x.eq_zero_iff _).mpr h)
  obtain ⟨g, hg⟩ := hunit.exists_right_inv
  have hfg : f * (g : K) = 1 := congrArg Subtype.val hg
  have hf0 : f ≠ 0 := left_ne_zero_of_mul_eq_one hfg
  have hgf : (g : K) = f⁻¹ := eq_inv_of_mul_eq_one_right hfg
  have hinv : f⁻¹ ∈ x.O := hgf ▸ g.2
  rw [val_of_mem x hinv]
  congr 1
  have h1 : x.ψ ⟨f, hf'⟩ * x.ψ ⟨f⁻¹, hinv⟩ = 1 := by
    rw [← map_mul, ← map_one x.ψ]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ hf0)
  exact eq_inv_of_mul_eq_one_right h1

/-- If `f(x) = 0` with `f ≠ 0`, then `f⁻¹(x) = ∞`. -/
theorem val_inv_of_eq_zero (x : EPlace K E) {f : K} (hf0 : f ≠ 0) (hf : x.val f = some 0) :
    x.val f⁻¹ = none := by
  obtain ⟨hf', hzero⟩ := (val_eq_some_iff x).mp hf
  have hnu : ¬ IsUnit (⟨f, hf'⟩ : x.O) := (x.eq_zero_iff _).mp hzero
  apply val_of_notMem
  intro hinv
  apply hnu
  exact ⟨⟨⟨f, hf'⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0),
    Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩

/-- If `f(x) = ∞` then `f⁻¹(x) = 0`. -/
theorem val_inv_of_eq_none (x : EPlace K E) {f : K} (hf : x.val f = none) :
    x.val f⁻¹ = some 0 := by
  have hf' : f ∉ x.O := by
    intro h
    rw [val_of_mem x h] at hf
    cases hf
  have hinv : f⁻¹ ∈ x.O := (x.O.mem_or_inv_mem f).resolve_left hf'
  rw [val_of_mem x hinv]
  congr 1
  rw [x.eq_zero_iff]
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hfg : f⁻¹ * (g : K) = 1 := congrArg Subtype.val hg
  have hgf : (g : K) = f := by
    have := eq_inv_of_mul_eq_one_right hfg
    rwa [inv_inv] at this
  exact hf' (hgf ▸ g.2)

end EPlace

end EPlace

section Limit

variable {K : Type*} [Field K] {E : Type*} [NormedField E]

/-- Convergence to a finite value via eventually finite values. -/
theorem tendstoP1_some_iff' {a : ℕ → Option E} {β : E} :
    TendstoP1 a (some β) ↔ ∃ α : ℕ → E, (∀ᶠ n in atTop, a n = some (α n)) ∧
      Tendsto α atTop (𝓝 β) := by
  constructor
  · intro h
    have hev : ∀ᶠ n in atTop, ∃ α, a n = some α := by
      filter_upwards [h 1 one_pos] with n hn
      obtain ⟨α, hα, -⟩ := hn
      exact ⟨α, hα⟩
    classical
    let α : ℕ → E := fun n => if hn : ∃ α, a n = some α then hn.choose else 0
    have hα : ∀ᶠ n in atTop, a n = some (α n) := by
      filter_upwards [hev] with n hn
      simp only [α, dif_pos hn]
      exact hn.choose_spec
    refine ⟨α, hα, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((h ε hε).and hα)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨⟨α', hα', hlt⟩, hαn⟩ := hN n hn
    rw [hαn] at hα'
    cases hα'
    rwa [dist_eq_norm]
  · rintro ⟨α, hα, hlim⟩ ε hε
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨N, hN⟩ := hlim ε hε
    filter_upwards [hα, eventually_ge_atTop N] with n hn hnN
    exact ⟨α n, hn, by rw [← dist_eq_norm]; exact hN n hnN⟩

/-- **Diagonal subsequence**: for a sequence of families of `E`-valued places of a countable
field whose finite values lie in a sequentially compact class, there is a subsequence along
which all values converge in `ℙ¹(E)`. -/
theorem exists_limit [Countable K] {ι : Type*} [Countable ι] [Nonempty ι] {Good : E → Prop}
    (hcpt : ∀ a : ℕ → E, (∀ n, Good (a n)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop))
    (x : ℕ → ι → EPlace K E) (hgood : ∀ n i f α, (x n i).val f = some α → Good α) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∃ ξ : ι → K → Option E,
      ∀ i f, TendstoP1 (fun n => (x (D n) i).val f) (ξ i f) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat (ι × K)
  let P : ℕ → (ℕ → ℕ) → Prop := fun k φ =>
    ∃ b, TendstoP1 (fun n => (x (φ n) (e k).1).val (e k).2) b
  have hP : ∀ k (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P k (φ ∘ ψ) := by
    intro k φ _
    obtain ⟨ψ, hψ, b, hb⟩ := exists_tendstoP1 hcpt
      (fun n => (x (φ n) (e k).1).val (e k).2) (fun n α hα => hgood _ _ _ _ hα)
    exact ⟨ψ, hψ, b, hb⟩
  have hmono : ∀ k (φ : ℕ → ℕ) (ψ : ℕ → ℕ), P k φ → Tendsto ψ atTop atTop → P k (φ ∘ ψ) := by
    rintro k φ ψ ⟨b, hb⟩ hψ
    exact ⟨b, hb.comp_of_tendsto hψ⟩
  obtain ⟨D, hD, hDk⟩ := exists_diagonal hP hmono
  have hlim : ∀ k, ∃ b, TendstoP1 (fun n => (x (D n) (e k).1).val (e k).2) b := by
    intro k
    obtain ⟨χ, hχ, φ, ⟨b, hb⟩, hDφ⟩ := hDk k
    refine ⟨b, (hb.comp_of_tendsto hχ).congr_eventually ?_⟩
    filter_upwards [eventually_gt_atTop k] with n hn
    simp only [Function.comp]
    rw [hDφ n hn]
  choose b hb using hlim
  refine ⟨D, hD, fun i f => b (he (i, f)).choose, fun i f => ?_⟩
  have := hb (he (i, f)).choose
  rw [(he (i, f)).choose_spec] at this
  exact this

end Limit

end AbcAdaptation.Tripod.Fermat.Proper.Source.Local

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source.Local

open Filter Topology

section Limit

variable {K : Type*} [Field K] {E : Type*} [NormedField E]
variable {x : ℕ → EPlace K E} {ξ : K → Option E}

/-- Limits of values are additive. -/
theorem limit_add (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f g : K} {α β : E}
    (hf : ξ f = some α) (hg : ξ g = some β) : ξ (f + g) = some (α + β) := by
  have hf' := h f
  have hg' := h g
  rw [hf, tendstoP1_some_iff'] at hf'
  rw [hg, tendstoP1_some_iff'] at hg'
  obtain ⟨a, ha, hla⟩ := hf'
  obtain ⟨b, hb, hlb⟩ := hg'
  refine (h (f + g)).unique (tendstoP1_some_iff'.mpr ⟨fun n => a n + b n, ?_, hla.add hlb⟩)
  filter_upwards [ha, hb] with n hna hnb
  exact (x n).val_add hna hnb

/-- Limits of values are multiplicative. -/
theorem limit_mul (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f g : K} {α β : E}
    (hf : ξ f = some α) (hg : ξ g = some β) : ξ (f * g) = some (α * β) := by
  have hf' := h f
  have hg' := h g
  rw [hf, tendstoP1_some_iff'] at hf'
  rw [hg, tendstoP1_some_iff'] at hg'
  obtain ⟨a, ha, hla⟩ := hf'
  obtain ⟨b, hb, hlb⟩ := hg'
  refine (h (f * g)).unique (tendstoP1_some_iff'.mpr ⟨fun n => a n * b n, ?_, hla.mul hlb⟩)
  filter_upwards [ha, hb] with n hna hnb
  exact (x n).val_mul hna hnb

theorem limit_neg (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} {α : E}
    (hf : ξ f = some α) : ξ (-f) = some (-α) := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  refine (h (-f)).unique (tendstoP1_some_iff'.mpr ⟨fun n => -a n, ?_, hla.neg⟩)
  filter_upwards [ha] with n hna
  exact (x n).val_neg hna

theorem limit_one (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ξ 1 = some 1 :=
  (h 1).unique (tendstoP1_some_iff'.mpr ⟨fun _ => 1,
    Eventually.of_forall fun n => (x n).val_one, tendsto_const_nhds⟩)

theorem limit_zero (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ξ 0 = some 0 :=
  (h 0).unique (tendstoP1_some_iff'.mpr ⟨fun _ => 0,
    Eventually.of_forall fun n => (x n).val_zero, tendsto_const_nhds⟩)

/-- `ξ f = 0` implies `ξ f⁻¹ = ∞`. -/
theorem limit_inv_of_eq_zero (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K}
    (hf0 : f ≠ 0) (hf : ξ f = some 0) : ξ f⁻¹ = none := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  refine (h f⁻¹).unique fun R => ?_
  have hsmall : ∀ᶠ n in atTop, ‖a n‖ < (max R 1)⁻¹ := by
    have := (tendsto_norm_zero.comp hla).eventually (gt_mem_nhds (a := (max R 1)⁻¹)
      (by positivity))
    simpa using this
  filter_upwards [ha, hsmall] with n hn hsm α hα
  by_cases h0 : a n = 0
  · rw [h0] at hn
    rw [(x n).val_inv_of_eq_zero hf0 hn] at hα
    cases hα
  · rw [(x n).val_inv_of_ne_zero hn h0] at hα
    cases hα
    rw [norm_inv]
    have hpos : 0 < ‖a n‖ := norm_pos_iff.mpr h0
    have h1 : 1 ≤ max R 1 := le_max_right _ _
    have h2 : max R 1 < ‖a n‖⁻¹ := by
      rw [lt_inv_comm₀ (by linarith) hpos]
      exact hsm
    exact lt_of_le_of_lt (le_max_left _ _) h2

/-- `ξ f = ∞` implies `ξ f⁻¹ = 0`. -/
theorem limit_inv_of_eq_none (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K}
    (hf : ξ f = none) : ξ f⁻¹ = some 0 := by
  have hf' := h f
  rw [hf] at hf'
  refine (h f⁻¹).unique (fun ε hε => ?_)
  filter_upwards [hf' ε⁻¹] with n hn
  cases hv : (x n).val f with
  | none => exact ⟨0, (x n).val_inv_of_eq_none hv, by simpa using hε⟩
  | some α =>
    have hα := hn α hv
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp only [norm_zero] at hα
      have : 0 < ε⁻¹ := inv_pos.mpr hε
      linarith
    refine ⟨α⁻¹, (x n).val_inv_of_ne_zero hv hα0, ?_⟩
    rw [sub_zero, norm_inv]
    exact (inv_lt_comm₀ hε (norm_pos_iff.mpr hα0)).mp hα

/-- **The limit valuation subring** `O_ξ = {f | ξ f ≠ ∞}`. -/
def limitSubring (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ValuationSubring K where
  carrier := {f | ξ f ≠ none}
  add_mem' {f g} hf hg := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp hg
    simp [limit_add h hα hβ]
  zero_mem' := by simp [limit_zero h]
  mul_mem' {f g} hf hg := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp hg
    simp [limit_mul h hα hβ]
  one_mem' := by simp [limit_one h]
  neg_mem' {f} hf := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    simp [limit_neg h hα]
  mem_or_inv_mem' f := by
    by_cases hf : ξ f = none
    · right
      simp [limit_inv_of_eq_none h hf]
    · exact Or.inl hf

theorem mem_limitSubring (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} :
    f ∈ limitSubring h ↔ ξ f ≠ none := Iff.rfl

/-- **Bounds away from `0`, `1`, `∞`**: if `ξ f ∉ {0, 1, ∞}`, then eventually
`|log ‖f(x n)‖|` and `|log ‖f(x n) − 1‖|` are bounded. -/
theorem eventually_abs_log_le (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} {β : E}
    (hf : ξ f = some β) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (x n).val f = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  have hb0 : 0 < ‖β‖ := norm_pos_iff.mpr hβ0
  have hb1 : 0 < ‖β - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hβ1)
  set δ := min ‖β‖ ‖β - 1‖ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hclose : ∀ᶠ n in atTop, ‖a n - β‖ < δ := by
    have := (Metric.tendsto_nhds.mp hla) δ hδpos
    simpa [dist_eq_norm] using this
  refine ⟨max (|Real.log (‖β‖ / 2)|) (|Real.log (‖β‖ * 2)|) +
    max (|Real.log (‖β - 1‖ / 2)|) (|Real.log (‖β - 1‖ * 2)|), ?_⟩
  filter_upwards [ha, hclose] with n hn hc
  have hδ1 : δ ≤ ‖β‖ / 2 := by
    rw [hδ]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδ2 : δ ≤ ‖β - 1‖ / 2 := by
    rw [hδ]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hlog : ∀ {t A B : ℝ}, 0 < A → A ≤ t → t ≤ B → |Real.log t| ≤ max |Real.log A| |Real.log B| :=
    fun {t A B} hA hAt htB => abs_le_max_abs_abs (Real.log_le_log hA hAt)
      (Real.log_le_log (hA.trans_le hAt) htB)
  have hnear : ∀ {u v : E}, ‖u - v‖ < ‖v‖ / 2 → ‖v‖ / 2 ≤ ‖u‖ ∧ ‖u‖ ≤ ‖v‖ * 2 := by
    intro u v huv
    have h1 : ‖v‖ ≤ ‖u‖ + ‖u - v‖ := by
      calc ‖v‖ = ‖u - (u - v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖u‖ + ‖u - v‖ := norm_sub_le _ _
    have h2 : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
      calc ‖u‖ = ‖v + (u - v)‖ := by rw [add_sub_cancel]
        _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
    constructor <;> nlinarith [norm_nonneg v, norm_nonneg (u - v)]
  obtain ⟨h1, h2⟩ := hnear (u := a n) (v := β) (lt_of_lt_of_le hc hδ1)
  have hc' : ‖(a n - 1) - (β - 1)‖ < ‖β - 1‖ / 2 := by
    rw [sub_sub_sub_cancel_right]
    exact lt_of_lt_of_le hc hδ2
  obtain ⟨h3, h4⟩ := hnear hc'
  refine ⟨a n, hn, ?_, ?_, ?_, ?_⟩
  · have := hlog (by positivity) h1 h2
    have h0 : 0 ≤ max |Real.log (‖β - 1‖ / 2)| |Real.log (‖β - 1‖ * 2)| :=
      le_max_of_le_left (abs_nonneg _)
    linarith
  · have := hlog (by positivity) h3 h4
    have h0 : 0 ≤ max |Real.log (‖β‖ / 2)| |Real.log (‖β‖ * 2)| :=
      le_max_of_le_left (abs_nonneg _)
    linarith
  · intro h0
    rw [h0, norm_zero] at h1
    linarith
  · intro h0
    rw [h0, sub_self, norm_zero] at h3
    linarith

end Limit


end AbcAdaptation.Tripod.Fermat.Proper.Source.Local

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source

open Local Filter Topology
open scoped Classical IntermediateField

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluation lands in the actual full residue-image field, as in the fixed carrier. -/
noncomputable def evalF (x : QbarPoint K) : x.P.1 →+* x.fieldOf :=
  (x.σ.comp x.P.residue).codRestrict x.fieldOf fun f =>
    x.eval_mem_fieldOf f.1 f.2

@[simp] theorem coe_evalF (x : QbarPoint K) (f : x.P.1) :
    (evalF x f : Qbar) = x.eval f.1 f.2 := rfl

/-- The finite-dimensionality input is exactly the pre-existing `hRF`. -/
theorem pointFieldFinite {N : ℕ} (M : Model N) (hRF : ResiduesFinite M)
    (x : QbarPoint M.K) : FiniteDimensional ℚ x.fieldOf := by
  letI : FiniteDimensional ℚ x.P.ResidueField := hRF x.P
  exact x.σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional

section EPlaces

variable {E : Type*} [NormedField E]

/-- A complete point-field embedding gives a genuine valued place. -/
noncomputable def pointEPlace (x : QbarPoint K) (τ : x.fieldOf →+* E) : EPlace K E where
  O := x.P.1
  ψ := τ.comp (evalF x)
  eq_zero_iff f := by
    change τ (evalF x f) = 0 ↔ ¬ IsUnit f
    rw [map_eq_zero_iff τ τ.injective]
    have heval : evalF x f = 0 ↔ x.P.residue f = 0 := by
      constructor
      · intro h
        apply x.σ.injective
        have hz : (evalF x f : Qbar) = 0 :=
          congrArg (fun a : x.fieldOf => (a : Qbar)) h
        exact (coe_evalF x f).symm.trans (hz.trans (map_zero x.σ).symm)
      · intro h
        apply Subtype.ext
        change x.σ (x.P.residue f) = 0
        rw [h, map_zero]
    rw [heval]
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.P.1) f = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem pointEPlace_val_of_mem (x : QbarPoint K) (τ : x.fieldOf →+* E) {f : K}
    (hf : f ∈ x.P.1) : (pointEPlace x τ).val f = some (τ (evalF x ⟨f, hf⟩)) :=
  EPlace.val_of_mem _ hf

end EPlaces

/-- The degree over `ℚ_p` of the image of an algebraic number of degree `≤ d`. -/
theorem natDegree_minpoly_padic_le {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [NumberField F]
    (τ : F →+* PadicAlgCl p) (a : F) :
    (minpoly ℚ_[p] (τ a)).natDegree ≤ Module.finrank ℚ F := by
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hne : (minpoly ℚ a).map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have hdvd : minpoly ℚ_[p] (τ a) ∣ (minpoly ℚ a).map (algebraMap ℚ ℚ_[p]) := by
    refine minpoly.dvd _ _ ?_
    rw [Polynomial.aeval_map_algebraMap]
    have := congrArg τ.toRatAlgHom (minpoly.aeval ℚ a)
    rw [map_zero, ← Polynomial.aeval_algHom_apply] at this
    exact this
  calc (minpoly ℚ_[p] (τ a)).natDegree
      ≤ ((minpoly ℚ a).map (algebraMap ℚ ℚ_[p])).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hne
    _ = (minpoly ℚ a).natDegree := Polynomial.natDegree_map _
    _ ≤ Module.finrank ℚ F := minpoly.natDegree_le a

/-- Countability follows from the finite simple-function-field presentation in `M`. -/
theorem model_countable {N : ℕ} (M : Model N) : Countable M.K := by
  let t : M.K := M.u
  haveI : FiniteDimensional ℚ⟮t⟯ M.K := M.finite_u
  haveI : Countable (Polynomial ℚ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Polynomial.cardinalMk_le_max (R := ℚ)).trans (by simp)
  haveI : Countable ℚ⟮t⟯ := by
    have hsurj : Function.Surjective fun pq : Polynomial ℚ × Polynomial ℚ =>
        (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) pq.1 /
          Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) pq.2 : ℚ⟮t⟯) := by
      rintro ⟨y, hy⟩
      obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ y).mp hy
      refine ⟨(r, s), Subtype.ext ?_⟩
      change ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) r : ℚ⟮t⟯) : M.K) /
          ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) s : ℚ⟮t⟯) : M.K) = _
      have h1 : ∀ f : Polynomial ℚ,
          ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) f : ℚ⟮t⟯) : M.K) =
            Polynomial.aeval t f := fun f => by
        have := Polynomial.aeval_algHom_apply (IntermediateField.val ℚ⟮t⟯)
          (IntermediateField.AdjoinSimple.gen ℚ t) f
        exact this.symm
      rw [h1, h1]
    exact hsurj.countable
  exact Finsupp.Countable.of_moduleFinite (R := ℚ⟮t⟯) (M := M.K)

/-! ### Enumerating embeddings -/

/-- A surjection `Fin d → (ℚ(x) →+* E)` onto the embeddings of the field of definition of a
point of degree `≤ d`. -/
theorem exists_surj_embeddings {E : Type*} [Field E] [CharZero E] [IsAlgClosed E]
    (x : QbarPoint K) [FiniteDimensional ℚ x.fieldOf] {d : ℕ} (hd : x.degree ≤ d) :
    ∃ e : Fin d → (x.fieldOf →+* E), Function.Surjective e := by
  letI : NumberField x.fieldOf := {}
  have hcard : Fintype.card (x.fieldOf →+* E) ≤ d := by
    rw [NumberField.Embeddings.card]
    exact hd
  haveI : Nonempty (x.fieldOf →+* E) := inferInstance
  refine ⟨fun i => if h : (i : ℕ) < Fintype.card (x.fieldOf →+* E) then
      (Fintype.equivFin (x.fieldOf →+* E)).symm ⟨i, h⟩ else Classical.arbitrary _, fun τ => ?_⟩
  set j := Fintype.equivFin (x.fieldOf →+* E) τ
  refine ⟨⟨j, lt_of_lt_of_le j.2 hcard⟩, ?_⟩
  simp only [j.2, dif_pos]
  exact (Fintype.equivFin (x.fieldOf →+* E)).symm_apply_apply τ

/-! ### Limit places -/

section LimitPlaces

variable {E : Type*} [NormedField E] [CharZero E]

/-- `E`-valued places map rational numbers to themselves. -/
theorem EPlace.val_ratCast (y : EPlace K E) (hQ : ∀ q : ℚ, (q : K) ∈ y.O) (q : ℚ) :
    y.val (q : K) = some (q : E) := by
  rw [EPlace.val_of_mem y (hQ q)]
  congr 1
  have hden : ((q.den : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have h1 : y.ψ ⟨(q : K), hQ q⟩ * (q.den : E) = (q.num : E) := by
    have h2 : (⟨(q : K), hQ q⟩ : y.O) * (q.den : y.O) = (q.num : y.O) := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, SubringClass.coe_intCast]
      exact_mod_cast Rat.mul_den_eq_num q
    have := congrArg y.ψ h2
    rwa [map_mul, map_natCast, map_intCast] at this
  have hq : (q : E) = (q.num : E) / (q.den : E) := Rat.cast_def q
  rw [hq, eq_div_iff hden]
  exact h1

variable {y : ℕ → EPlace K E} {ξ : K → Option E}

/-- The limit of a convergent sequence of `E`-valued places with `ℚ ⊆ O` contains `ℚ`. -/
theorem ratCast_mem_limitSubring (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) (q : ℚ) : (q : K) ∈ limitSubring h := by
  rw [mem_limitSubring]
  have : ξ (q : K) = some (q : E) := (h (q : K)).unique
    ((tendstoP1_some_iff' (E := E)).mpr ⟨fun _ => (q : E),
      Eventually.of_forall fun n => EPlace.val_ratCast (y n) (hQ n) q, tendsto_const_nhds⟩)
  rw [this]
  exact Option.some_ne_none _

/-- The limit place (if the limit valuation ring is not everything). -/
noncomputable def limitPlace (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) : Option (Place K) :=
  if hT : limitSubring h = ⊤ then none
  else some ⟨limitSubring h, hT, ratCast_mem_limitSubring hQ h⟩

/-- **Bounds away from `0`, `1`, `∞` along a convergent sequence**, for a function which is
regular, invertible, and with `φ − 1` invertible, at the limit place. -/
theorem eventually_bounded_of_limitPlace (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) {φ : K} (hφ0 : φ ≠ 0) (hφ1 : φ ≠ 1)
    (hP : ∀ P, limitPlace hQ h = some P → φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (y n).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := by
  have hmem : ∀ g, (g = φ ∨ g = φ⁻¹ ∨ g = (φ - 1)⁻¹) → ξ g ≠ none := by
    intro g hg
    rw [← mem_limitSubring h]
    by_cases hT : limitSubring h = ⊤
    · rw [hT]
      exact ValuationSubring.mem_top g
    · have := hP ⟨limitSubring h, hT, ratCast_mem_limitSubring hQ h⟩ (by
        simp only [limitPlace, dif_neg hT])
      rcases hg with rfl | rfl | rfl
      · exact this.1
      · exact this.2.1
      · exact this.2.2
  obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp (hmem φ (Or.inl rfl))
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hmem φ⁻¹ (Or.inr (Or.inl rfl)) (limit_inv_of_eq_zero h hφ0 hβ)
  have hβ1 : β ≠ 1 := by
    rintro rfl
    have hm1 : ξ (-1) = some (-1) := limit_neg h (limit_one h)
    have h2 : ξ (φ - 1) = some 0 := by
      rw [sub_eq_add_neg, limit_add h hβ hm1, add_neg_cancel]
    exact hmem (φ - 1)⁻¹ (Or.inr (Or.inr rfl))
      (limit_inv_of_eq_zero h (sub_ne_zero.mpr hφ1) h2)
  exact eventually_abs_log_le h hβ hβ0 hβ1

end LimitPlaces

/-! ### The subsequence -/

section Subsequence

/-- One round of the diagonal argument, along a given subsequence. -/
theorem exists_subseq_limit [Countable K] {E : Type*} [NormedField E] {Good : E → Prop}
    (hcpt : ∀ a : ℕ → E, (∀ n, Good (a n)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop))
    {d : ℕ} [NeZero d] (y : ℕ → Fin d → EPlace K E)
    (hgood : ∀ n i f α, (y n i).val f = some α → Good α) (D₀ : ℕ → ℕ) (hD₀ : StrictMono D₀) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ D = D₀ ∘ ψ) ∧
      ∃ ξ : Fin d → K → Option E, ∀ i f, TendstoP1 (fun n => (y (D n) i).val f) (ξ i f) := by
  obtain ⟨ψ, hψ, ξ, hξ⟩ := exists_limit hcpt (fun n => y (D₀ n))
    (fun n i f α h => hgood _ _ _ _ h)
  exact ⟨D₀ ∘ ψ, hD₀.comp hψ, ⟨ψ, hψ, rfl⟩, ξ, hξ⟩

/-- Convergence is preserved along further subsequences. -/
theorem tendstoP1_comp_subseq {E : Type*} [NormedField E] {a : ℕ → Option E} {b : Option E}
    (h : TendstoP1 a b) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) : TendstoP1 (a ∘ ψ) b :=
  h.comp_of_tendsto hψ.tendsto_atTop

end Subsequence


end AbcAdaptation.Tripod.Fermat.Proper.Source

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source

open Local Filter Topology
open scoped Classical IntermediateField

/-! ### The main compactness statement -/

section Main

/-- Primes carry their primality as an instance (local). -/
local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **The compactness argument of [GenEll], Theorem 2.1**: for points `x_n` of degree `≤ d` and a
finite set `V` of primes, there are a subsequence and a finite set `T` of places of `M.K` (the
algebraic limit points at the places of `V ∪ {∞}`) such that every `φ ≠ 0, 1` regular and
invertible, with `φ − 1` invertible, at the places of `T` has values at all embeddings of the
fields of definition into `ℂ` and into `ℚ̄_p` (`p ∈ V`) bounded away from `0`, `1`, `∞`, along a
tail of the subsequence. -/
theorem exists_subseq_bounded {N : ℕ} (M : Model N) (hRF : ResiduesFinite M)
    (V : Finset Nat.Primes) {d : ℕ} (x : ℕ → QbarPoint M.K)
    (hx : ∀ n, (x n).degree ≤ d) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∃ T : Finset (Place M.K), ∀ φ : M.K, φ ≠ 0 → φ ≠ 1 →
      (∀ P ∈ T, φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1) →
      ∃ C : ℝ, ∀ᶠ n in atTop, ∃ hφ : φ ∈ (x (D n)).P.1,
        (x (D n)).eval φ hφ ≠ 0 ∧ (x (D n)).eval φ hφ ≠ 1 ∧
        (∀ σ : (x (D n)).fieldOf →+* ℂ,
          |Real.log ‖σ (evalF (x (D n)) ⟨φ, hφ⟩)‖| ≤ C ∧
          |Real.log ‖σ (evalF (x (D n)) ⟨φ, hφ⟩) - 1‖| ≤ C) ∧
        ∀ p ∈ V, ∀ τ : (x (D n)).fieldOf →+* PadicAlgCl (p : ℕ),
          |Real.log ‖τ (evalF (x (D n)) ⟨φ, hφ⟩)‖| ≤ C ∧
          |Real.log ‖τ (evalF (x (D n)) ⟨φ, hφ⟩) - 1‖| ≤ C := by
  letI : Countable M.K := model_countable M
  letI (n : ℕ) : FiniteDimensional ℚ (x n).fieldOf := pointFieldFinite M hRF (x n)
  letI (n : ℕ) : NumberField (x n).fieldOf := {}
  have hd : 0 < d := lt_of_lt_of_le (Module.finrank_pos (R := ℚ) (M := (x 0).fieldOf)) (hx 0)
  haveI : NeZero d := ⟨hd.ne'⟩
  -- enumerate the embeddings
  choose eC heC using fun n => exists_surj_embeddings (E := ℂ) (x n) (hx n)
  choose eP heP using fun (p : Nat.Primes) n =>
    exists_surj_embeddings (E := PadicAlgCl (p : ℕ)) (x n) (hx n)
  set yC : ℕ → Fin d → EPlace M.K ℂ := fun n i => pointEPlace (x n) (eC n i) with hyC
  set yP : ∀ p : Nat.Primes, ℕ → Fin d → EPlace M.K (PadicAlgCl (p : ℕ)) :=
    fun p n i => pointEPlace (x n) (eP p n i) with hyP
  have hQ : ∀ n (q : ℚ), (q : M.K) ∈ (x n).P.1 := fun n q => (x n).P.2.2 q
  have hgoodP : ∀ (p : Nat.Primes) n i f α, (yP p n i).val f = some α →
      (minpoly ℚ_[(p : ℕ)] α).natDegree ≤ d := by
    intro p n i f α h
    obtain ⟨hf, rfl⟩ := (EPlace.val_eq_some_iff _).mp h
    exact (natDegree_minpoly_padic_le _ _).trans (hx n)
  -- successive rounds
  have key : ∀ W : Finset Nat.Primes, ∃ D : ℕ → ℕ, StrictMono D ∧
      (∃ ξ : Fin d → M.K → Option ℂ, ∀ i f, TendstoP1 (fun n => (yC (D n) i).val f) (ξ i f)) ∧
      ∀ p ∈ W, ∃ ξ : Fin d → M.K → Option (PadicAlgCl (p : ℕ)),
        ∀ i f, TendstoP1 (fun n => (yP p (D n) i).val f) (ξ i f) := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      obtain ⟨D, hD, -, ξ, hξ⟩ := exists_subseq_limit (Good := fun _ : ℂ => True)
        (fun a _ => exists_tendsto_or_tendsto_norm_atTop a) yC (fun _ _ _ _ _ => trivial)
        id strictMono_id
      exact ⟨D, hD, ⟨ξ, hξ⟩, by simp⟩
    | insert p W hpW ih =>
      obtain ⟨D, hD, ⟨ξC, hξC⟩, hW⟩ := ih
      obtain ⟨D', hD', ⟨ψ, hψ, rfl⟩, ξ, hξ⟩ :=
        exists_subseq_limit (Good := fun α : PadicAlgCl (p : ℕ) =>
          (minpoly ℚ_[(p : ℕ)] α).natDegree ≤ d)
          (fun a ha => PadicAlgCl.exists_tendsto_or_tendsto_norm_atTop d a ha) (yP p)
          (hgoodP p) D hD
      refine ⟨D ∘ ψ, hD', ⟨ξC, fun i f => tendstoP1_comp_subseq (hξC i f) hψ⟩, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqW
      · exact ⟨ξ, hξ⟩
      · obtain ⟨ξq, hξq⟩ := hW q hqW
        exact ⟨ξq, fun i f => tendstoP1_comp_subseq (hξq i f) hψ⟩
  obtain ⟨D, hD, ⟨ξC, hC⟩, hPV⟩ := key V
  choose ξP hξP using hPV
  have hQC : ∀ i n (q : ℚ), (q : M.K) ∈ (yC (D n) i).O := fun i n q => hQ (D n) q
  have hQP : ∀ p i n (q : ℚ), (q : M.K) ∈ (yP p (D n) i).O := fun p i n q => hQ (D n) q
  -- the limit places
  set T : Finset (Place M.K) :=
    (Finset.univ.biUnion fun i => (limitPlace (hQC i) (hC i)).toFinset) ∪
      V.attach.biUnion fun p => Finset.univ.biUnion fun i =>
        (limitPlace (hQP p.1 i) (hξP p.1 p.2 i)).toFinset with hT
  refine ⟨D, hD, T, fun φ hφ0 hφ1 hφT => ?_⟩
  have hbC : ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (yC (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := fun i =>
    eventually_bounded_of_limitPlace (hQC i) (hC i) hφ0 hφ1 fun P hP => hφT P (by
      rw [hT, Finset.mem_union, Finset.mem_biUnion]
      exact Or.inl ⟨i, Finset.mem_univ _, by simp [hP]⟩)
  have hbP : ∀ p : V, ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (yP p.1 (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := fun p i =>
    eventually_bounded_of_limitPlace (hQP p.1 i) (hξP p.1 p.2 i) hφ0 hφ1 fun P hP => hφT P (by
      rw [hT, Finset.mem_union, Finset.mem_biUnion]
      right
      rw [Finset.mem_biUnion]
      exact ⟨p, Finset.mem_attach _ _, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hP]⟩⟩)
  choose CC hCC using hbC
  choose CP hCP using hbP
  set C : ℝ := ∑ i, |CC i| + ∑ p ∈ V.attach, ∑ i, |CP p i| with hCdef
  have hCC_le : ∀ i, CC i ≤ C := fun i => by
    have h1 : |CC i| ≤ ∑ i, |CC i| :=
      Finset.single_le_sum (f := fun i => |CC i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ p ∈ V.attach, ∑ i, |CP p i| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self (CC i)]
  have hCP_le : ∀ p i, CP p i ≤ C := fun p i => by
    have h1 : |CP p i| ≤ ∑ i, |CP p i| :=
      Finset.single_le_sum (f := fun i => |CP p i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |CP p i| ≤ ∑ p ∈ V.attach, ∑ i, |CP p i| :=
      Finset.single_le_sum (f := fun p => ∑ i, |CP p i|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_attach _ p)
    have h3 : 0 ≤ ∑ i, |CC i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self (CP p i)]
  refine ⟨C, ?_⟩
  have hevC := Filter.eventually_all.mpr hCC
  have hevP : ∀ᶠ n in atTop, ∀ p ∈ V.attach, ∀ i, ∃ α, (yP p.1 (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ CP p i ∧ |Real.log ‖α - 1‖| ≤ CP p i ∧ α ≠ 0 ∧ α ≠ 1 :=
    (Filter.eventually_all_finset _).mpr fun p _ => Filter.eventually_all.mpr (hCP p)
  filter_upwards [hevC, hevP] with n hnC hnP
  obtain ⟨α₀, hα₀, -, -, hα₀0, hα₀1⟩ := hnC ⟨0, hd⟩
  obtain ⟨hφmem, hα₀eq⟩ := (EPlace.val_eq_some_iff _).mp hα₀
  have hv0 : evalF (x (D n)) ⟨φ, hφmem⟩ ≠ 0 := fun h0 => hα₀0 (by
    rw [← hα₀eq]
    change eC (D n) ⟨0, hd⟩ (evalF (x (D n)) ⟨φ, hφmem⟩) = 0
    rw [h0, map_zero])
  have hv1 : evalF (x (D n)) ⟨φ, hφmem⟩ ≠ 1 := fun h0 => hα₀1 (by
    rw [← hα₀eq]
    change eC (D n) ⟨0, hd⟩ (evalF (x (D n)) ⟨φ, hφmem⟩) = 1
    rw [h0, map_one])
  refine ⟨hφmem, (fun h0 => hv0 (Subtype.ext h0)),
    (fun h1 => hv1 (Subtype.ext h1)), fun σ => ?_, fun p hp τ => ?_⟩
  · obtain ⟨i, rfl⟩ := heC (D n) σ
    obtain ⟨α, hα, h1, h2, -, -⟩ := hnC i
    rw [show (yC (D n) i).val φ = some (eC (D n) i (evalF (x (D n)) ⟨φ, hφmem⟩)) from
      pointEPlace_val_of_mem _ _ hφmem] at hα
    cases hα
    exact ⟨h1.trans (hCC_le i), h2.trans (hCC_le i)⟩
  · obtain ⟨i, rfl⟩ := heP p (D n) τ
    obtain ⟨α, hα, h1, h2, -, -⟩ := hnP ⟨p, hp⟩ (Finset.mem_attach _ _) i
    rw [show (yP p (D n) i).val φ = some (eP p (D n) i (evalF (x (D n)) ⟨φ, hφmem⟩)) from
      pointEPlace_val_of_mem _ _ hφmem] at hα
    cases hα
    exact ⟨h1.trans (hCP_le ⟨p, hp⟩ i), h2.trans (hCP_le ⟨p, hp⟩ i)⟩

end Main


/-- The fixed support is exactly `{2}`; every full point-field embedding is retained. -/
theorem localCompactness_source {N : ℕ} (M : Model N) (hRF : ResiduesFinite M) :
    LocalCompactness M := by
  intro d xs hxs
  let V : Finset Nat.Primes := {⟨2, Nat.prime_two⟩}
  obtain ⟨s, hs, T, hT⟩ := exists_subseq_bounded M hRF V xs hxs
  refine ⟨s, hs, T, fun φ h0 h1 hφT => ?_⟩
  obtain ⟨c, hc⟩ := hT φ h0 h1 hφT
  refine ⟨c, ?_⟩
  filter_upwards [hc] with n hn
  obtain ⟨hφ, hv0, hv1, hC, hP⟩ := hn
  refine ⟨hφ, hv0, hv1, ?_, ?_⟩
  · exact hC
  · exact hP ⟨2, Nat.prime_two⟩ (Finset.mem_singleton_self _)

end AbcAdaptation.Tripod.Fermat.Proper.Source

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem closedCompactnessSource {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : LocalCompactness M := by
  exact Source.localCompactness_source M hRF

end AbcAdaptation.Tripod.Fermat.Proper

theorem solution : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N),
  AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M →
    AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M → AbcAdaptation.Tripod.Fermat.Proper.LocalCompactness M :=
  AbcAdaptation.Tripod.Fermat.Proper.closedCompactnessSource
