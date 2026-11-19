namespace TateCurvesTheta

variable {K : Type*} [NormedField K]

structure IsUniformizer (π : K) : Prop where

  ne_zero : π ≠ 0

  norm_lt_one : ‖π‖ < 1

  generates : ∀ x : Kˣ, ∃ n : ℤ, ‖(x : K)‖ = ‖π‖ ^ n

namespace TateParameter

variable (t : TateParameter K) {π : K}

lemma exists_norm_q_eq_zpow (hπ : IsUniformizer π) : ∃ n : ℤ, ‖(t.q : K)‖ = ‖π‖ ^ n :=
  hπ.generates t.q

noncomputable def orderZ (hπ : IsUniformizer π) : ℤ :=
  Classical.choose (t.exists_norm_q_eq_zpow hπ)

lemma norm_q_eq_zpow (hπ : IsUniformizer π) : ‖(t.q : K)‖ = ‖π‖ ^ t.orderZ hπ :=
  Classical.choose_spec (t.exists_norm_q_eq_zpow hπ)

theorem orderZ_pos (hπ : IsUniformizer π) : 0 < t.orderZ hπ := by
  have hq : Real.log ‖(t.q : K)‖ < 0 := Real.log_neg t.norm_q_pos t.norm_lt_one
  have heq : Real.log ‖(t.q : K)‖ = (t.orderZ hπ : ℝ) * Real.log ‖π‖ := by
    rw [t.norm_q_eq_zpow hπ, Real.log_zpow]
  by_contra hcon
  rw [not_lt] at hcon
  have hcast : (t.orderZ hπ : ℝ) ≤ 0 := by exact_mod_cast hcon
  have hnonneg : (0 : ℝ) ≤ (t.orderZ hπ : ℝ) * Real.log ‖π‖ := by
    nlinarith [hπ.log_norm_neg.le]
  rw [heq] at hq
  linarith

noncomputable def toOrdered (hπ : IsUniformizer π) : OrderedTateParameter K :=
  { t with
    orderNat := (t.orderZ hπ).toNat
    orderNat_pos := by
      have := t.orderZ_pos hπ
      omega }
