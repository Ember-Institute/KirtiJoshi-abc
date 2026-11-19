/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Peripheral.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeQuadrants
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

/-!
# Monodromy around a lattice puncture

Lift the exponential map from a left half-plane to the covering. Its lifts on consecutive
strips follow the four quadrant lifts. Advancing by `2π i` acts by the commutator
`A⁻¹ B⁻¹ A B`.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} (U : LatticeComplementCover (periodPair t))


/-- The angle `α = arg t` of the lattice direction `t`. -/
noncomputable def α (t : ℍ) : ℝ := Complex.arg (t : ℂ)

theorem α_nonneg : 0 ≤ α t := Complex.arg_nonneg_iff.mpr t.im_pos.le
theorem α_le_pi : α t ≤ π := Complex.arg_le_pi _

theorem cy_exp (s : ℂ) : cy t (Complex.exp s) = Real.exp s.re * Real.sin s.im / t.im := by
  simp [cy, Complex.exp_im]

theorem cx_exp (s : ℂ) :
    cx t (Complex.exp s) = Real.exp s.re * (‖(t : ℂ)‖ * Real.sin (α t - s.im)) / t.im := by
  have ht := t.im_pos.ne'
  have h1 := Complex.norm_mul_cos_arg (t : ℂ)
  have h2 := Complex.norm_mul_sin_arg (t : ℂ)
  rw [cx, cy_exp, Real.sin_sub, mul_sub, ← mul_assoc, ← mul_assoc, α, h2, h1]
  simp only [Complex.exp_re, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp

theorem cx_exp_nonneg_iff (s : ℂ) : 0 ≤ cx t (Complex.exp s) ↔ 0 ≤ Real.sin (α t - s.im) := by
  have hpos : 0 < Real.exp s.re * ‖(t : ℂ)‖ / t.im :=
    div_pos (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (UpperHalfPlane.ne_zero t))) t.im_pos
  rw [cx_exp, show Real.exp s.re * (‖(t : ℂ)‖ * Real.sin (α t - s.im)) / t.im =
    Real.exp s.re * ‖(t : ℂ)‖ / t.im * Real.sin (α t - s.im) by ring]
  exact ⟨fun h ↦ nonneg_of_mul_nonneg_right h hpos |>.trans' le_rfl |> fun h' ↦ by
    by_contra hc; push Not at hc; nlinarith [mul_neg_of_pos_of_neg hpos hc],
    fun h ↦ mul_nonneg hpos.le h⟩

theorem cx_exp_nonpos_iff (s : ℂ) : cx t (Complex.exp s) ≤ 0 ↔ Real.sin (α t - s.im) ≤ 0 := by
  have hpos : 0 < Real.exp s.re * ‖(t : ℂ)‖ / t.im :=
    div_pos (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (UpperHalfPlane.ne_zero t))) t.im_pos
  rw [cx_exp, show Real.exp s.re * (‖(t : ℂ)‖ * Real.sin (α t - s.im)) / t.im =
    Real.exp s.re * ‖(t : ℂ)‖ / t.im * Real.sin (α t - s.im) by ring]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith [mul_pos hpos hc]
  · intro h; exact mul_nonpos_of_nonneg_of_nonpos hpos.le h

theorem cy_exp_nonneg_iff (s : ℂ) : 0 ≤ cy t (Complex.exp s) ↔ 0 ≤ Real.sin s.im := by
  have hpos : 0 < Real.exp s.re / t.im := div_pos (Real.exp_pos _) t.im_pos
  rw [cy_exp, show Real.exp s.re * Real.sin s.im / t.im = Real.exp s.re / t.im * Real.sin s.im by
    ring]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith [mul_neg_of_pos_of_neg hpos hc]
  · intro h; exact mul_nonneg hpos.le h

theorem cy_exp_nonpos_iff (s : ℂ) : cy t (Complex.exp s) ≤ 0 ↔ Real.sin s.im ≤ 0 := by
  have hpos : 0 < Real.exp s.re / t.im := div_pos (Real.exp_pos _) t.im_pos
  rw [cy_exp, show Real.exp s.re * Real.sin s.im / t.im = Real.exp s.re / t.im * Real.sin s.im by
    ring]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith [mul_pos hpos hc]
  · intro h; exact mul_nonpos_of_nonneg_of_nonpos hpos.le h

theorem sin_nonneg' {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π) : 0 ≤ Real.sin x :=
  Real.sin_nonneg_of_nonneg_of_le_pi h0 h1

theorem sin_nonpos' {x : ℝ} (h0 : x ≤ 0) (h1 : -π ≤ x) : Real.sin x ≤ 0 :=
  Real.sin_nonpos_of_nonpos_of_neg_pi_le h0 h1

theorem exp_mem_Q₁ {s : ℂ} (h0 : 0 ≤ s.im) (h1 : s.im ≤ α t) : Complex.exp s ∈ Q₁ t :=
  ⟨(cx_exp_nonneg_iff s).mpr (sin_nonneg' (by linarith) (by linarith [α_le_pi (t := t)])),
    (cy_exp_nonneg_iff s).mpr (sin_nonneg' h0 (by linarith [α_le_pi (t := t)]))⟩

theorem exp_mem_Q₂ {s : ℂ} (h0 : α t ≤ s.im) (h1 : s.im ≤ π) : Complex.exp s ∈ Q₂ t :=
  ⟨(cx_exp_nonpos_iff s).mpr (sin_nonpos' (by linarith) (by linarith [α_nonneg (t := t)])),
    (cy_exp_nonneg_iff s).mpr (sin_nonneg' (by linarith [α_nonneg (t := t)]) h1)⟩

theorem exp_mem_Q₃ {s : ℂ} (h0 : π ≤ s.im) (h1 : s.im ≤ π + α t) : Complex.exp s ∈ Q₃ t := by
  refine ⟨(cx_exp_nonpos_iff s).mpr (sin_nonpos' (by linarith [α_le_pi (t := t)])
    (by linarith)), (cy_exp_nonpos_iff s).mpr ?_⟩
  have : Real.sin s.im = -Real.sin (s.im - π) := by rw [Real.sin_sub_pi]; ring
  rw [this, neg_nonpos]
  exact sin_nonneg' (by linarith) (by linarith [α_le_pi (t := t)])

theorem exp_mem_Q₄ {s : ℂ} (h0 : π + α t ≤ s.im) (h1 : s.im ≤ 2 * π) : Complex.exp s ∈ Q₄ t := by
  refine ⟨(cx_exp_nonneg_iff s).mpr ?_, (cy_exp_nonpos_iff s).mpr ?_⟩
  · have : Real.sin (α t - s.im) = Real.sin (α t - s.im + 2 * π) := by
      rw [Real.sin_add_two_pi]
    rw [this]
    exact sin_nonneg' (by linarith [α_nonneg (t := t)]) (by linarith [α_le_pi (t := t)])
  · have : Real.sin s.im = -Real.sin (s.im - π) := by rw [Real.sin_sub_pi]; ring
    rw [this, neg_nonpos]
    exact sin_nonneg' (by linarith [α_nonneg (t := t)]) (by linarith)

theorem exp_sub_two_pi (s : ℂ) : Complex.exp (s - 2 * π * I) = Complex.exp s := by
  rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]

theorem exp_mem_Q₁' {s : ℂ} (h0 : 2 * π ≤ s.im) (h1 : s.im ≤ 2 * π + α t) :
    Complex.exp s ∈ Q₁ t := by
  rw [← exp_sub_two_pi s]
  exact exp_mem_Q₁ (by simp; linarith) (by simp; linarith)

/-! ### The half-plane and its strips -/

/-- The half-plane `{Re s < log r₀}`, mapped onto `D*` by `exp`. -/
def Hr (t : ℍ) : Set ℂ := {s | s.re < Real.log (r₀ t)}

/-- A strip of the half-plane. -/
def strip (t : ℍ) (θ₁ θ₂ : ℝ) : Set ℂ := {s | s.re < Real.log (r₀ t) ∧ θ₁ ≤ s.im ∧ s.im ≤ θ₂}

theorem isOpen_Hr : IsOpen (Hr t) := isOpen_lt continuous_re continuous_const

theorem convex_Hr : Convex ℝ (Hr t) := convex_halfSpace_re_lt _

theorem convex_strip (θ₁ θ₂ : ℝ) : Convex ℝ (strip t θ₁ θ₂) :=
  (convex_halfSpace_re_lt _).inter ((convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _))

theorem strip_subset {θ₁ θ₂ : ℝ} : strip t θ₁ θ₂ ⊆ Hr t := fun _ h ↦ h.1

theorem exp_mem_Dst {s : ℂ} (hs : s ∈ Hr t) : Complex.exp s ∈ Dst t := by
  refine ⟨?_, Complex.exp_ne_zero s⟩
  rw [mem_ball_zero_iff, Complex.norm_exp]
  calc Real.exp s.re < Real.exp (Real.log (r₀ t)) := Real.exp_lt_exp.mpr hs
    _ = r₀ t := Real.exp_log r₀_pos

theorem exp_mem_Ω {s : ℂ} (hs : s ∈ Hr t) : Complex.exp s ∈ ((periodPair t).lattice : Set ℂ)ᶜ :=
  Dst_notMem (exp_mem_Dst hs)

/-- A point of `Hr` with prescribed imaginary part. -/
noncomputable def pt (t : ℍ) (θ : ℝ) : ℂ := (Real.log (r₀ t) - 1 : ℝ) + θ * I

theorem pt_re (θ : ℝ) : (pt t θ).re = Real.log (r₀ t) - 1 := by simp [pt]
theorem pt_im (θ : ℝ) : (pt t θ).im = θ := by simp [pt]

theorem pt_mem_strip {θ θ₁ θ₂ : ℝ} (h1 : θ₁ ≤ θ) (h2 : θ ≤ θ₂) : pt t θ ∈ strip t θ₁ θ₂ :=
  ⟨by rw [pt_re]; linarith, by rw [pt_im]; exact h1, by rw [pt_im]; exact h2⟩

/-! ### The lift of the exponential -/

theorem exists_Sig : ∃ Sig : ℂ → ℍ, ContinuousOn Sig (Hr t) ∧
    (∀ s ∈ Hr t, U.ψ (Sig s) = Complex.exp s) ∧
    Sig (pt t (α t / 2)) = σ₁ U (Complex.exp (pt t (α t / 2))) := by
  have hmem : pt t (α t / 2) ∈ strip t 0 (α t) :=
    pt_mem_strip (by linarith [α_nonneg (t := t)]) (by linarith [α_nonneg (t := t)])
  exact U.covering.exists_lift_of_convex convex_Hr Complex.continuous_exp.continuousOn
    (fun s hs ↦ exp_mem_Ω hs) (strip_subset hmem)
    (ψ_σ₁ U (exp_mem_Dst (strip_subset hmem))
      (exp_mem_Q₁ (by rw [pt_im]; linarith [α_nonneg (t := t)])
        (by rw [pt_im]; linarith [α_nonneg (t := t)])))

/-- The lift `Sig` of `exp : Hr → D*` through `ψ`. -/
noncomputable def Sig : ℂ → ℍ := (exists_Sig U).choose

theorem continuousOn_Sig : ContinuousOn (Sig U) (Hr t) := (exists_Sig U).choose_spec.1

theorem ψ_Sig {s : ℂ} (hs : s ∈ Hr t) : U.ψ (Sig U s) = Complex.exp s :=
  (exists_Sig U).choose_spec.2.1 s hs

theorem Sig_base : Sig U (pt t (α t / 2)) = σ₁ U (Complex.exp (pt t (α t / 2))) :=
  (exists_Sig U).choose_spec.2.2

/-- Uniqueness of lifts of `exp` over a strip. -/
theorem Sig_eqOn {θ₁ θ₂ : ℝ} {σ : ℂ → ℍ} (hσ : ContinuousOn σ (strip t θ₁ θ₂))
    (hψ : ∀ s ∈ strip t θ₁ θ₂, U.ψ (σ s) = Complex.exp s) {s₀ : ℂ} (hs₀ : s₀ ∈ strip t θ₁ θ₂)
    (h₀ : Sig U s₀ = σ s₀) : EqOn (Sig U) σ (strip t θ₁ θ₂) :=
  U.covering.eqOn_of_lift (convex_strip θ₁ θ₂).isPreconnected
    ((continuousOn_Sig U).mono strip_subset) hσ
    (fun s hs ↦ by
      change U.ψ (Sig U s) ∈ _; rw [ψ_Sig U (strip_subset hs)]; exact exp_mem_Ω (strip_subset hs))
    (fun s hs ↦ by
      change U.ψ (Sig U s) = U.ψ (σ s); rw [ψ_Sig U (strip_subset hs), hψ s hs]) hs₀ h₀

theorem Sig_eq₁ : EqOn (Sig U) (σ₁ U ∘ Complex.exp) (strip t 0 (α t)) := by
  refine Sig_eqOn U ((continuousOn_σ₁ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₁ hs.2.1 hs.2.2⟩) (fun s hs ↦
    ψ_σ₁ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₁ hs.2.1 hs.2.2))
    (pt_mem_strip (by linarith [α_nonneg (t := t)]) (by linarith [α_nonneg (t := t)]))
    (Sig_base U)

theorem Sig_eq₂ : EqOn (Sig U) (σ₂ U ∘ Complex.exp) (strip t (α t) π) := by
  have hs : pt t (α t) ∈ strip t 0 (α t) := pt_mem_strip (α_nonneg) le_rfl
  have hs' : pt t (α t) ∈ strip t (α t) π := pt_mem_strip le_rfl α_le_pi
  have hz := exp_mem_Dst (t := t) (strip_subset hs)
  have hq₁ := exp_mem_Q₁ (t := t) hs.2.1 hs.2.2
  have hq₂ := exp_mem_Q₂ (t := t) hs'.2.1 hs'.2.2
  refine Sig_eqOn U ((continuousOn_σ₂ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₂ hs.2.1 hs.2.2⟩) (fun s hs ↦
    ψ_σ₂ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₂ hs.2.1 hs.2.2)) hs' ?_
  rw [Sig_eq₁ U hs, Function.comp_apply, Function.comp_apply,
    seam₁₂ U hz (le_antisymm hq₂.1 hq₁.1) hq₁.2]

theorem Sig_eq₃ : EqOn (Sig U) (σ₃ U ∘ Complex.exp) (strip t π (π + α t)) := by
  have hs : pt t π ∈ strip t (α t) π := pt_mem_strip α_le_pi le_rfl
  have hs' : pt t π ∈ strip t π (π + α t) := pt_mem_strip le_rfl (by linarith [α_nonneg (t := t)])
  have hz := exp_mem_Dst (t := t) (strip_subset hs)
  have hq₂ := exp_mem_Q₂ (t := t) hs.2.1 hs.2.2
  have hq₃ := exp_mem_Q₃ (t := t) hs'.2.1 hs'.2.2
  refine Sig_eqOn U ((continuousOn_σ₃ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₃ hs.2.1 hs.2.2⟩) (fun s hs ↦
    ψ_σ₃ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₃ hs.2.1 hs.2.2)) hs' ?_
  rw [Sig_eq₂ U hs, Function.comp_apply, Function.comp_apply,
    seam₂₃ U hz hq₂.1 (le_antisymm hq₃.2 hq₂.2)]

theorem Sig_eq₄ : EqOn (Sig U) (σ₄ U ∘ Complex.exp) (strip t (π + α t) (2 * π)) := by
  have hs : pt t (π + α t) ∈ strip t π (π + α t) :=
    pt_mem_strip (by linarith [α_nonneg (t := t)]) le_rfl
  have hs' : pt t (π + α t) ∈ strip t (π + α t) (2 * π) :=
    pt_mem_strip le_rfl (by linarith [α_le_pi (t := t)])
  have hz := exp_mem_Dst (t := t) (strip_subset hs)
  have hq₃ := exp_mem_Q₃ (t := t) hs.2.1 hs.2.2
  have hq₄ := exp_mem_Q₄ (t := t) hs'.2.1 hs'.2.2
  refine Sig_eqOn U ((continuousOn_σ₄ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₄ hs.2.1 hs.2.2⟩) (fun s hs ↦
    ψ_σ₄ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₄ hs.2.1 hs.2.2)) hs' ?_
  rw [Sig_eq₃ U hs, Function.comp_apply, Function.comp_apply,
    seam₃₄ U hz (le_antisymm hq₃.1 hq₄.1) hq₃.2]

theorem Sig_eq₅ :
    EqOn (Sig U) (fun s ↦ Cm U • σ₁ U (Complex.exp s)) (strip t (2 * π) (2 * π + α t)) := by
  have hs : pt t (2 * π) ∈ strip t (π + α t) (2 * π) :=
    pt_mem_strip (by linarith [α_le_pi (t := t)]) le_rfl
  have hs' : pt t (2 * π) ∈ strip t (2 * π) (2 * π + α t) :=
    pt_mem_strip le_rfl (by linarith [α_nonneg (t := t)])
  have hz := exp_mem_Dst (t := t) (strip_subset hs)
  have hq₄ := exp_mem_Q₄ (t := t) hs.2.1 hs.2.2
  have hq₁ := exp_mem_Q₁' (t := t) hs'.2.1 hs'.2.2
  refine Sig_eqOn U ((continuous_const_smul _).comp_continuousOn
    ((continuousOn_σ₁ U).comp Complex.continuous_exp.continuousOn fun s hs ↦
    ⟨exp_mem_Dst (strip_subset hs), exp_mem_Q₁' hs.2.1 hs.2.2⟩)) (fun s hs ↦ by
      rw [ψ_Cm_smul, ψ_σ₁ U (exp_mem_Dst (strip_subset hs)) (exp_mem_Q₁' hs.2.1 hs.2.2)])
    hs' ?_
  rw [Sig_eq₄ U hs, Function.comp_apply, seam₄₁ U hz hq₁.1 (le_antisymm hq₄.2 hq₁.2)]

theorem add_two_pi_mem_Hr {s : ℂ} (hs : s ∈ Hr t) : s + 2 * π * I ∈ Hr t := by
  simpa [Hr] using hs

/-- **The monodromy relation** `Sig (s + 2π i) = C • Sig s`. -/
theorem Sig_add_two_pi {s : ℂ} (hs : s ∈ Hr t) : Sig U (s + 2 * π * I) = Cm U • Sig U s := by
  have hcont₁ : ContinuousOn (fun s ↦ Sig U (s + 2 * π * I)) (Hr t) :=
    (continuousOn_Sig U).comp (continuous_add_const _).continuousOn fun s hs ↦ add_two_pi_mem_Hr hs
  have hcont₂ : ContinuousOn (fun s ↦ Cm U • Sig U s) (Hr t) :=
    (continuous_const_smul _).comp_continuousOn (continuousOn_Sig U)
  set s₀ := pt t (α t / 2)
  have hs₀ : s₀ ∈ strip t 0 (α t) :=
    pt_mem_strip (by linarith [α_nonneg (t := t)]) (by linarith [α_nonneg (t := t)])
  have hs₀' : s₀ + 2 * π * I ∈ strip t (2 * π) (2 * π + α t) := by
    refine ⟨by simpa using hs₀.1, ?_, ?_⟩ <;> simp [s₀, pt_im] <;> linarith [α_nonneg (t := t)]
  have h₀ : Sig U (s₀ + 2 * π * I) = Cm U • Sig U s₀ := by
    rw [Sig_eq₅ U hs₀', Sig_eq₁ U hs₀, Function.comp_apply]
    simp only
    rw [← exp_sub_two_pi (s₀ + 2 * π * I), add_sub_cancel_right]
  have := U.covering.eqOn_of_lift convex_Hr.isPreconnected hcont₁ hcont₂
    (fun s hs ↦ by
      change U.ψ (Sig U (s + 2 * π * I)) ∈ _
      rw [ψ_Sig U (add_two_pi_mem_Hr hs)]; exact exp_mem_Ω (add_two_pi_mem_Hr hs))
    (fun s hs ↦ by
      change U.ψ (Sig U (s + 2 * π * I)) = U.ψ (Cm U • Sig U s)
      rw [ψ_Sig U (add_two_pi_mem_Hr hs), ψ_Cm_smul, ψ_Sig U hs, ← exp_sub_two_pi (s + _),
        add_sub_cancel_right])
    (strip_subset hs₀) h₀
  exact this hs

/-- `Sig` is holomorphic. -/
theorem differentiableOn_Sig : DifferentiableOn ℂ (fun s ↦ (Sig U s : ℂ)) (Hr t) := by
  intro s hs
  have him := (Sig U s).im_pos
  have hstrict : HasStrictDerivAt U.Ψ (deriv U.Ψ (Sig U s)) (Sig U s) :=
    (U.differentiableOn.analyticAt (isOpen_upper.mem_nhds him)).hasStrictDerivAt
  refine (HolomorphicInverse.differentiableAt_of_comp_eq (f := U.Ψ) (g := Complex.exp)
    hstrict (U.deriv_ne_zero _ him)
    ((continuous_coe.comp_continuousOn (continuousOn_Sig U)).continuousAt
      (isOpen_Hr.mem_nhds hs)) ?_ Complex.differentiableAt_exp).differentiableWithinAt
  filter_upwards [isOpen_Hr.mem_nhds hs] with v hv
  exact ψ_Sig U hv

end Peripheral

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
