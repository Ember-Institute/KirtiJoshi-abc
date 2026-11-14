/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

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
