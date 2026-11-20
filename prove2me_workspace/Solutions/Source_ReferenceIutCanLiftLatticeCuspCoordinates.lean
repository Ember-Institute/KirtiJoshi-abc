/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Cusp.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeCommutatorTrace
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Tactic.Group

set_option autoImplicit false

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} (U : LatticeComplementCover (periodPair t))

/-- **Descent along `exp`.** A `2πi`-periodic function holomorphic on the half-plane
`{Re s < log r₀}` defines a holomorphic function `w ↦ E (log w)` on the punctured disc, with
`E s = (E ∘ log) (exp s)`. -/
theorem differentiableOn_comp_log {E : ℂ → ℂ} (hE : DifferentiableOn ℂ E (Hr t))
    (hper : ∀ s ∈ Hr t, E (s + 2 * π * I) = E s) :
    DifferentiableOn ℂ (fun w ↦ E (Complex.log w)) (Dst t) ∧
      ∀ s ∈ Hr t, E (Complex.log (Complex.exp s)) = E s := by
  have hperZ : ∀ s ∈ Hr t, ∀ k : ℤ, E (s + k * (2 * π * I)) = E s := by
    intro s hs k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have h1 := hper _ (add_int_mem_Hr hs n)
      rw [← ih, ← h1]; congr 1; push_cast; ring
    | pred n ih =>
      have h1 := hper _ (add_int_mem_Hr hs (-n - 1))
      rw [← ih, ← h1]; congr 1; push_cast; ring
  have hexp : ∀ s ∈ Hr t, E (Complex.log (Complex.exp s)) = E s := by
    intro s hs
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      (Complex.exp_log (Complex.exp_ne_zero s))
    rw [hn, hperZ s hs n]
  refine ⟨fun p hp ↦ ?_, hexp⟩
  set s₁ := Complex.log p
  have hs₁ := log_mem_Hr hp
  have hps : Complex.exp s₁ = p := Complex.exp_log hp.2
  have hexps : HasStrictDerivAt Complex.exp (Complex.exp s₁) s₁ :=
    Complex.hasStrictDerivAt_exp s₁
  have hne : Complex.exp s₁ ≠ 0 := Complex.exp_ne_zero s₁
  set L := hexps.localInverse Complex.exp (Complex.exp s₁) s₁ hne
  have hL : HasStrictDerivAt L (Complex.exp s₁)⁻¹ (Complex.exp s₁) :=
    hexps.to_localInverse hne
  have hLs : L (Complex.exp s₁) = s₁ := (hexps.eventually_left_inverse hne).self_of_nhds
  have hLc : ContinuousAt L (Complex.exp s₁) := hL.hasDerivAt.continuousAt
  have hev : ∀ᶠ q in 𝓝 (Complex.exp s₁), E (Complex.log q) = E (L q) := by
    filter_upwards [hexps.eventually_right_inverse hne,
      hLc.preimage_mem_nhds (by rw [hLs]; exact isOpen_Hr.mem_nhds hs₁)] with q hq1 hq2
    rw [← hexp _ hq2, hq1]
  rw [← hps]
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
  have h1 : DifferentiableAt ℂ E (L (Complex.exp s₁)) := by
    rw [hLs]; exact hE.differentiableAt (isOpen_Hr.mem_nhds hs₁)
  exact h1.comp (Complex.exp s₁) hL.hasDerivAt.differentiableAt

/-- The monodromy `C` is conjugate to a translation. -/
theorem exists_conj_translation :
    ∃ M : SL(2, ℝ), ∃ κ : ℝ, κ ≠ 0 ∧ ∀ z : ℍ,
      (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ := by
  have htr := trace_Cm U
  -- a conjugate with vanishing lower-left entry
  obtain ⟨M, hM⟩ : ∃ M : SL(2, ℝ), (M⁻¹ * Cm U * M) 1 0 = 0 := by
    by_cases hc : Cm U 1 0 = 0
    · exact ⟨1, by simpa using hc⟩
    · obtain ⟨η, hη⟩ := exists_real_fix (Cm U) (by rw [htr]; norm_num) hc
      exact ⟨conjFix η, by rw [conjFix_lowerLeft]; exact hη⟩
  set N := M⁻¹ * Cm U * M
  have hNtr : N 0 0 + N 1 1 = -2 := by
    have := trSL_conj M (Cm U); rw [htr] at this; exact this
  have hNdet : N 0 0 * N 1 1 = 1 := by have := det_SL N; rw [hM] at this; linarith
  have ha : N 0 0 = -1 := by nlinarith [sq_nonneg (N 0 0 + 1)]
  have hd : N 1 1 = -1 := by linarith
  refine ⟨M, -N 0 1, ?_, fun z ↦ ?_⟩
  · intro h0
    have h0' : N 0 1 = 0 := by linarith
    apply Cm_smul_ne U (M • UpperHalfPlane.I)
    have hN : ∀ z : ℍ, N • z = z := fun z ↦ by
      apply UpperHalfPlane.ext
      rw [coe_SL2R_smul, hM, ha, hd, h0']
      push_cast
      simp
    have := hN UpperHalfPlane.I
    calc Cm U • M • UpperHalfPlane.I = M • (N • UpperHalfPlane.I) := by
          simp only [N, ← mul_smul]; congr 1; group
      _ = M • UpperHalfPlane.I := by rw [this]
  · rw [coe_SL2R_smul, hM, ha, hd]
    push_cast
    field_simp; ring

theorem isDiscrete_exp_preimage_one : IsDiscrete (Complex.exp ⁻¹' {1}) := by
  rw [isDiscrete_iff_discreteTopology]
  exact (Complex.isCoveringMapOn_exp 1 (by simp)).discreteTopology_fiber

/-- A continuous function `k` on a preconnected set with `exp (k s) = 1` is constant. -/
theorem const_of_exp_eq_one {S : Set ℂ} (hS : IsPreconnected S) {k : ℂ → ℂ}
    (hk : ContinuousOn k S) (h1 : ∀ s ∈ S, Complex.exp (k s) = 1) {x y : ℂ} (hx : x ∈ S)
    (hy : y ∈ S) : k x = k y :=
  hS.constant_of_mapsTo isDiscrete_exp_preimage_one hk (fun s hs ↦ h1 s hs) hx hy

theorem translation_zpow {M : SL(2, ℝ)} {κ : ℝ}
    (hM : ∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ) (m : ℤ) (z : ℍ) :
    (((M⁻¹ * Cm U * M) ^ m • z : ℍ) : ℂ) = z + m * κ := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, ih, hM]; push_cast; ring
  | pred n ih =>
    have h := hM ((M⁻¹ * Cm U * M) ^ (-(n : ℤ) - 1) • z)
    rw [← mul_smul, ← zpow_one_add, show (1 : ℤ) + (-n - 1) = -n by ring, ih] at h
    push_cast at h ⊢
    linear_combination -h

/-- The lift in the normalised coordinate `M⁻¹ τ`. -/
noncomputable def τ' (M : SL(2, ℝ)) (s : ℂ) : ℂ := ((M⁻¹ • Sig U s : ℍ) : ℂ)

theorem τ'_im_pos (M : SL(2, ℝ)) (s : ℂ) : 0 < (τ' U M s).im := (M⁻¹ • Sig U s).im_pos

theorem differentiableOn_τ' (M : SL(2, ℝ)) : DifferentiableOn ℂ (τ' U M) (Hr t) := by
  have hS := differentiableOn_Sig U
  have : DifferentiableOn ℂ (fun s ↦ ((M⁻¹ 0 0 : ℂ) * (Sig U s : ℂ) + M⁻¹ 0 1) /
      ((M⁻¹ 1 0 : ℂ) * (Sig U s : ℂ) + M⁻¹ 1 1)) (Hr t) :=
    (((differentiableOn_const _).mul hS).add_const _).div
      (((differentiableOn_const _).mul hS).add_const _)
      fun s _ ↦ denom_SL2R_ne_zero M⁻¹ (Sig U s).im_pos
  exact this.congr fun s _ ↦ coe_SL2R_smul M⁻¹ (Sig U s)

theorem τ'_add_two_pi {M : SL(2, ℝ)} {κ : ℝ}
    (hM : ∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ) {s : ℂ} (hs : s ∈ Hr t) :
    τ' U M (s + 2 * π * I) = τ' U M s + κ := by
  rw [τ', Sig_add_two_pi U hs, τ', ← hM, ← mul_smul, ← mul_smul]
  congr 2; group

theorem ψ_Cm_zpow_smul (m : ℤ) (ν : ℍ) : U.ψ ((Cm U) ^ m • ν) = U.ψ ν := by
  induction m using Int.induction_on generalizing ν with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, ih, ψ_Cm_smul]
  | pred n ih =>
    rw [show (-(n : ℤ) - 1) = -(n : ℤ) + (-1) by ring, zpow_add, zpow_neg_one, mul_smul, ih]
    have := ψ_Cm_smul U ((Cm U)⁻¹ • ν)
    rw [smul_inv_smul] at this
    exact this.symm

theorem conj_zpow_smul (M : SL(2, ℝ)) (m : ℤ) (ν : ℍ) :
    M • ((M⁻¹ * Cm U * M) ^ m • (M⁻¹ • ν)) = (Cm U) ^ m • ν := by
  have := conj_zpow (i := m) (a := M⁻¹) (b := Cm U)
  rw [inv_inv] at this
  rw [this, ← mul_smul, ← mul_smul]
  congr 1; group

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
