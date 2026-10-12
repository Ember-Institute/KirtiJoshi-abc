/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTateGain
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource

/-!
source-id: IUT-COR312-INITIAL-THETA-TATE-GAIN-BASE-CHANGE
source: `iut` completion embedding and ramification transfer from
`refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean`, together with
the local completion-valued gain in `IutInitialThetaTateGain.lean`.
fidelity: cancels the positive relative-ramification power after explicit norm
transport certificates are supplied for the two ratio values and the Tate
parameter.  The descent equations remain inputs; this module does not prove
that the actual Vélu ratios descend to the base completion.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open NumberField
open scoped NumberField Valued

universe u

noncomputable section

variable {F Kt : Type u} [Field F] [NumberField F]
variable [Field Kt] [NumberField Kt] [Algebra F Kt]

/-!
The real inequality below is the algebraic core of the finite-place transport.
It is stated separately so that the cancellation of the ramification power is
auditable independently of any choice of local fields.
-/

theorem ratio_mul_bound_of_positive_power_transport
    {ell e : ℕ} {a₁ a₂ q a₁' a₂' q' : ℝ}
    (he : e ≠ 0)
    (hq0 : 0 ≤ q)
    (ha₁ : a₁' = a₁ ^ e) (ha₂ : a₂' = a₂ ^ e) (hq : q' = q ^ e)
    (hlocal : (a₁' * a₂') ^ 4 ≤ q' ^ (ell - 1)) :
    (a₁ * a₂) ^ 4 ≤ q ^ (ell - 1) := by
  have hlocal' := hlocal
  rw [ha₁, ha₂, hq, ← mul_pow, ← pow_mul, ← pow_mul] at hlocal'
  have hpow : ((a₁ * a₂) ^ 4) ^ e ≤ (q ^ (ell - 1)) ^ e := by
    rw [← pow_mul, ← pow_mul]
    convert hlocal' using 1 <;> simp [Nat.mul_comm]
  have h1 : 0 ≤ (a₁ * a₂) ^ 4 := by positivity
  have h2 : 0 ≤ q ^ (ell - 1) := by positivity
  exact (pow_le_pow_iff_left₀ h1 h2 he).mp hpow

/-- Transport the completion-valued local gain to a base completion.

The three norm equations are explicit source certificates.  They are written
for `iutEmbedCompletion` so that the relative ramification index is the one
attached to the actual pair of finite places.  A later source adapter may
instantiate them for descended Vélu ratios and the Tate parameter.
-/
theorem iutCompletion_ratio_mul_bound_to_base
    {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    {ell : ℕ}
    {r₁ r₂ q : w.maximalIdeal.adicCompletion F}
    (hlocal :
      (‖iutEmbedCompletion hvw r₁‖ * ‖iutEmbedCompletion hvw r₂‖) ^ 4 ≤
        ‖iutEmbedCompletion hvw q‖ ^ (ell - 1))
    (hr₁ : ‖iutEmbedCompletion hvw r₁‖ =
      ‖r₁‖ ^ iutRelativeRamificationIndex (v := v) (w := w))
    (hr₂ : ‖iutEmbedCompletion hvw r₂‖ =
      ‖r₂‖ ^ iutRelativeRamificationIndex (v := v) (w := w))
    (hq : ‖iutEmbedCompletion hvw q‖ =
      ‖q‖ ^ iutRelativeRamificationIndex (v := v) (w := w)) :
    (‖r₁‖ * ‖r₂‖) ^ 4 ≤ ‖q‖ ^ (ell - 1) := by
  let e := iutRelativeRamificationIndex (v := v) (w := w)
  have he : e ≠ 0 := iutRelativeRamificationIndex_ne_zero hvw
  have h := ratio_mul_bound_of_positive_power_transport
    (ell := ell) (e := e) he
    (norm_nonneg q)
    hr₁ hr₂ hq hlocal
  simpa [e] using h

/-- Logarithmic form of the transported base-place gain. -/
theorem iutCompletion_ratio_mul_log_bound_to_base
    {ell : ℕ} {r₁ r₂ q : ℝ} (hell : 1 ≤ ell)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hq : 0 < q)
    (hbound : (r₁ * r₂) ^ 4 ≤ q ^ (ell - 1)) :
    Real.log (r₁ * r₂) ≤
      (((ell : ℝ) - 1) / 4) * Real.log q := by
  have hlog :=
    (Real.strictMonoOn_log.le_iff_le
      (pow_pos (mul_pos hr₁ hr₂) 4)
      (pow_pos hq (ell - 1))).2 hbound
  rw [Real.log_pow, Real.log_pow] at hlog
  have hcast : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    rw [Nat.cast_sub hell]
    norm_num
  rw [hcast] at hlog
  norm_num at hlog
  nlinarith

end

end JoshiTeich.Act1Scene1
