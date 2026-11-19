/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/FEtCovering.lean
-/
import Solutions.Source_ReferenceIutCanLiftAnalyticChart
import Solutions.Source_ReferenceIutCanLiftCoveringSections
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped BigOperators

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  (ι₀ : A →ₐ[ℂ] (ℍ → ℂ))

variable (B) in
/-- The total space: points `(τ, ψ)` with `ψ` a point of `B` over `χ_τ`. -/
abbrev Tot : Type _ := {p : ℍ × (B → ℂ) // ∃ ψ : Over B (pt ι₀ p.1), ⇑ψ.1 = p.2}

/-- The projection to `ℍ`. -/
def proj (p : Tot B ι₀) : ℍ := p.1.1

theorem continuous_proj : Continuous (proj ι₀ (B := B)) :=
  continuous_fst.comp continuous_subtype_val

variable {ι₀}

/-- **The points of `B` form a covering of `ℍ`.** -/
theorem isCoveringMap_proj (hhol : ∀ a, HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ) :
    IsCoveringMap (proj ι₀ (B := B)) := by
  classical
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine isCoveringMapOn_of_sections (by simp) (continuous_proj ι₀).continuousOn ?_ ?_
  · -- local injectivity
    rintro ⟨⟨τ₁, φ⟩, hφ⟩ -
    obtain ⟨V, hVo, hτV, -, b₀, ε, σ, hε, hsep, -, hroot, -, -, hσb₀⟩ :=
      exists_chart ι₀ hhol hcount τ₁ (hloc τ₁)
    obtain ⟨ψ, hψ⟩ := hφ
    obtain ⟨j, hj⟩ := hroot τ₁ hτV ψ
    set g : Tot B ι₀ → ℂ := fun p ↦ p.1.2 b₀ - σ j (proj ι₀ p) b₀
    have hg : ContinuousOn g (proj ι₀ ⁻¹' V) :=
      ((continuous_apply b₀).comp (continuous_snd.comp continuous_subtype_val)).continuousOn.sub
        ((hσb₀ j).comp (continuous_proj ι₀).continuousOn (mapsTo_preimage _ _))
    have hWo : IsOpen (proj ι₀ ⁻¹' V ∩ g ⁻¹' ball 0 (ε / 2)) :=
      hg.isOpen_inter_preimage (hVo.preimage (continuous_proj ι₀)) isOpen_ball
    refine ⟨_, hWo.mem_nhds ⟨hτV, ?_⟩, ?_⟩
    · have hψ' : ⇑ψ.1 = φ := hψ
      simp only [mem_preimage, mem_ball, dist_zero_right, g, proj]
      rw [← hψ', hj, sub_self, norm_zero]; positivity
    · rintro ⟨⟨τ, φ₁⟩, hφ₁⟩ ⟨h1V, h1g⟩ ⟨⟨τ', φ₂⟩, hφ₂⟩ ⟨h2V, h2g⟩ (hττ' : τ = τ')
      subst hττ'
      obtain ⟨ψ₁, hψ₁⟩ := hφ₁
      obtain ⟨ψ₂, hψ₂⟩ := hφ₂
      replace hψ₁ : ⇑ψ₁.1 = φ₁ := hψ₁
      replace hψ₂ : ⇑ψ₂.1 = φ₂ := hψ₂
      obtain ⟨k, hk⟩ := hroot τ h1V ψ₁
      obtain ⟨l, hl⟩ := hroot τ h2V ψ₂
      simp only [mem_preimage, mem_ball, dist_zero_right, g, proj] at h1g h2g
      rw [← hψ₁, hk] at h1g
      rw [← hψ₂, hl] at h2g
      have hkj : k = j := by
        by_contra h
        have := hsep τ h1V k j h
        linarith
      have hlj : l = j := by
        by_contra h
        have := hsep τ h2V l j h
        linarith
      apply Subtype.ext
      simp only [Prod.mk.injEq, true_and]
      rw [← hψ₁, ← hψ₂, hk, hl, hkj, hlj]
  · -- local sections
    intro x _
    obtain ⟨V, hVo, hxV, hVpre, b₀, ε, σ, hε, hsep, hex, hroot, -, hσc, -⟩ :=
      exists_chart ι₀ hhol hcount x (hloc x)
    refine ⟨V, hVo, hxV, subset_univ _, hVpre, fun e he ↦ ?_⟩
    obtain ⟨ψe, hψe⟩ := e.2
    obtain ⟨j, hj⟩ := hroot _ he ψe
    have hmem : ∀ v ∈ V, ∃ ψ : Over B (pt ι₀ v), ⇑ψ.1 = σ j v := fun v hv ↦ hex v hv j
    let s : ℍ → Tot B ι₀ := fun v ↦ if hv : v ∈ V then ⟨(v, σ j v), hmem v hv⟩ else e
    refine ⟨s, ?_, fun v hv ↦ by simp [s, hv, proj], ?_⟩
    · rw [Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff]
      have : ContinuousOn (fun v : ℍ ↦ (v, σ j v)) V :=
        continuousOn_id.prodMk (continuousOn_pi.mpr (hσc j))
      refine this.congr fun v hv ↦ ?_
      simp [s, hv]
    · have heV : proj ι₀ e ∈ V := he
      simp only [s, heV, dif_pos]
      apply Subtype.ext
      have h2 : σ j e.1.1 = e.1.2 := hj.symm.trans hψe
      simp only [proj, h2]

/-- **Lifting**: every point `ψ₀` over `χ_{τ₀}` extends to a holomorphic family of points. -/
theorem exists_lift (hhol : ∀ a, HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    (τ₀ : ℍ) (ψ₀ : Over B (pt ι₀ τ₀)) :
    ∃ ι : ℍ → B → ℂ, (∀ τ, ∃ ψ : Over B (pt ι₀ τ), ⇑ψ.1 = ι τ) ∧ ι τ₀ = ⇑ψ₀.1 ∧
      ∀ b, HolH fun τ ↦ ι τ b := by
  classical
  have hcov := isCoveringMap_proj hhol hcount hloc
  set e₀ : Tot B ι₀ := ⟨(τ₀, ⇑ψ₀.1), ψ₀, rfl⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts ⟨id, continuous_id⟩ τ₀ e₀ rfl
  have hFp : ∀ τ, (F τ).1.1 = τ := fun τ ↦ congrFun hF τ
  have key : ∀ p : Tot B ι₀, ∀ τ, p.1.1 = τ → ∃ ψ : Over B (pt ι₀ τ), ⇑ψ.1 = p.1.2 := by
    rintro p τ rfl; exact p.2
  refine ⟨fun τ ↦ (F τ).1.2, fun τ ↦ key (F τ) τ (hFp τ), by change (F τ₀).1.2 = _; rw [hF0],
    fun b ↦ ?_⟩
  · intro z hz
    set τ₁ : ℍ := ⟨z, hz⟩
    obtain ⟨V, hVo, hτV, hVpre, b₀, ε, σ, hε, hsep, hex, hroot, hσd, hσc, -⟩ :=
      exists_chart ι₀ hhol hcount τ₁ (hloc τ₁)
    obtain ⟨ψ₁, hψ₁⟩ := key (F τ₁) τ₁ (hFp τ₁)
    obtain ⟨j, hj⟩ := hroot τ₁ hτV ψ₁
    have hmem : ∀ v ∈ V, ∃ ψ : Over B (pt ι₀ v), ⇑ψ.1 = σ j v := fun v hv ↦ hex v hv j
    let s : ℍ → Tot B ι₀ := fun v ↦ if hv : v ∈ V then ⟨(v, σ j v), hmem v hv⟩ else F τ₁
    have hsc : ContinuousOn s V := by
      rw [Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff]
      have : ContinuousOn (fun v : ℍ ↦ (v, σ j v)) V :=
        continuousOn_id.prodMk (continuousOn_pi.mpr (hσc j))
      refine this.congr fun v hv ↦ ?_
      simp [s, hv]
    have hFs : EqOn F s V := hcov.eqOn_of_comp_eqOn hVpre F.continuous.continuousOn hsc
      (fun v hv ↦ by simp [s, hv, proj, hFp]) hτV (by
        simp only [s, hτV, dif_pos]
        apply Subtype.ext
        exact Prod.ext (hFp τ₁) (hψ₁.symm.trans hj))
    have hVz : ((↑) : ℍ → ℂ) '' V ∈ 𝓝 z :=
      (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap V hVo).mem_nhds ⟨τ₁, hτV, rfl⟩
    have hd : DifferentiableAt ℂ (fun w ↦ σ j (ofComplex w) b) z := (hσd j b).differentiableAt hVz
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hVz] with w hw
    obtain ⟨τ, hτ, rfl⟩ := hw
    simp only [ofComplex_apply]
    rw [hFs hτ]
    simp [s, hτ]

/-- A holomorphic function on `ℍ` is continuous. -/
theorem HolH.continuous {f : ℍ → ℂ} (hf : HolH f) :
    Continuous f := by
  have := hf.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos
  simpa [Function.comp_def, ofComplex_apply] using this

variable (ι₀) in
/-- A lift: a continuous family of points of `B` over the points `χ_τ`. -/
structure IsLift (ι : ℍ → B → ℂ) : Prop where
  pt : ∀ τ, ∃ ψ : Over B (pt ι₀ τ), ⇑ψ.1 = ι τ
  cont : ∀ b, Continuous fun τ ↦ ι τ b

/-- The section of `proj` given by a lift. -/
def IsLift.sec {ι : ℍ → B → ℂ} (h : IsLift ι₀ ι) (τ : ℍ) : Tot B ι₀ := ⟨(τ, ι τ), h.pt τ⟩

theorem IsLift.continuous_sec {ι : ℍ → B → ℂ} (h : IsLift ι₀ ι) : Continuous h.sec :=
  (continuous_id.prodMk (continuous_pi h.cont)).subtype_mk _

/-- **Uniqueness of lifts.** -/
theorem IsLift.eq (hcov : IsCoveringMap (proj ι₀ (B := B))) {ι ι' : ℍ → B → ℂ}
    (h : IsLift ι₀ ι) (h' : IsLift ι₀ ι') {τ₀ : ℍ} (h0 : ι τ₀ = ι' τ₀) : ι = ι' := by
  have := hcov.eq_of_comp_eq h.continuous_sec h'.continuous_sec rfl τ₀
    (Subtype.ext (Prod.ext rfl h0))
  funext τ
  exact congrArg (fun p : Tot B ι₀ ↦ p.1.2) (congrFun this τ)

/-- Lifts through every point exist and are holomorphic. -/
theorem exists_isLift (hhol : ∀ a, HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    (τ₀ : ℍ) (ψ₀ : Over B (pt ι₀ τ₀)) :
    ∃ ι : ℍ → B → ℂ, IsLift ι₀ ι ∧ ι τ₀ = ⇑ψ₀.1 ∧ ∀ b, HolH fun τ ↦ ι τ b := by
  obtain ⟨ι, h1, h2, h3⟩ := exists_lift hhol hcount hloc τ₀ ψ₀
  exact ⟨ι, ⟨h1, fun b ↦ (h3 b).continuous⟩, h2, h3⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
