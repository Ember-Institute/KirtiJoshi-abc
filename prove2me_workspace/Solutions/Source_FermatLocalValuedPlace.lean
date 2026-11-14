/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/
import Solutions.Source_FermatLocalProjectiveConvergence
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Set.Countable

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
