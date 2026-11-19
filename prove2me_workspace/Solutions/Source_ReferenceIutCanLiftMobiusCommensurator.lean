/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/TheoremG.lean
-/
import Solutions.Source_ReferenceIutCanLiftDeckGroup
import Solutions.Source_ReferenceIutCanLiftMobius

set_option autoImplicit false

/-!
A Möbius transformation realizing an automorphism of a finite étale cover normalizes the lift
stabilizer. Counting the fiber at a point proves that this stabilizer is commensurable with the
uniformization group.
-/

open Polynomial Set
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  {ι₀ : A →ₐ[ℂ] (ℍ → ℂ)} {n : ℕ}

private theorem finite_over {τ : ℍ} (hloc : LocPres ι₀ (B := B) n τ) : Finite (Over B (pt ι₀ τ)) := by
  classical
  obtain ⟨b₀, F, δ, hFm, -, hF, hδ, hpres⟩ := hloc
  have hmaps : ∀ ψ : Over B (pt ι₀ τ),
      ψ.1 b₀ ∈ (F.map (pt ι₀ τ : A →+* ℂ)).roots.toFinset := fun ψ ↦ by
    rw [Multiset.mem_toFinset, mem_roots ((hFm.map _).ne_zero)]; exact ψ.isRoot hF
  exact Finite.of_injective (fun ψ ↦ (⟨ψ.1 b₀, hmaps ψ⟩ :
    (F.map (pt ι₀ τ : A →+* ℂ)).roots.toFinset))
    fun ψ ψ' h ↦ Over.ext_of_apply_eq hδ hpres (congrArg Subtype.val h)

variable {W : WeierstrassCurve ℂ} {G₁ G₂ : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- The stabiliser of a lift. -/
def liftStab (ι : ℍ → B → ℂ) : Subgroup SL(2, ℝ) where
  carrier := {δ | ∀ τ b, ι (δ • τ) b = ι τ b}
  mul_mem' {δ δ'} h h' τ b := by rw [mul_smul, h, h']
  one_mem' τ b := by rw [one_smul]
  inv_mem' {δ} h τ b := by
    have := h (δ⁻¹ • τ) b
    rw [smul_inv_smul] at this
    exact this.symm

/-- **Möbius transformations realising automorphisms lie in the commensurator.** -/
theorem mobius_mem_commensurator [W.IsElliptic] (h : IsUniformization W G₁ G₂ π) {x y : A}
    (hx : ∀ τ, ι₀ x τ = (π τ).1) (hy : ∀ τ, ι₀ y τ = (π τ).2)
    (hxy : ∀ χ χ' : A →ₐ[ℂ] ℂ, χ x = χ' x → χ y = χ' y → χ = χ')
    (hhol : ∀ a, HolH (ι₀ a))
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    (σ : B ≃ₐ[ℂ] B) {ι : ℍ → B → ℂ} (hι : IsLift ι₀ ι) {g : SL(2, ℝ)}
    (hg : ∀ τ b, ι τ (σ b) = ι (g • τ) b) :
    g ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {G₁, G₂}) := by
  classical
  set S := liftStab ι
  set Γ := Subgroup.closure {G₁, G₂}
  have hcov := isCoveringMap_proj hhol hcount hloc
  -- `S ≤ ±Γ`
  have hSpm : S ≤ IsUniformization.pmGroup G₁ G₂ := by
    intro δ hδ
    change ∀ τ b, ι (δ • τ) b = ι τ b at hδ
    refine h.mem_pmGroup_of_deck (D := δ) fun w ↦ Subtype.ext (Prod.ext ?_ ?_)
    · change (π (δ • w : ℍ)).1 = (π w).1
      simpa only [hι.apply_algebraMap, hx] using hδ w (algebraMap A B x)
    · change (π (δ • w : ℍ)).2 = (π w).2
      simpa only [hι.apply_algebraMap, hy] using hδ w (algebraMap A B y)
  -- `g` normalises `S`
  have hg' : ∀ τ b, ι (g⁻¹ • τ) b = ι τ (σ.symm b) := fun τ b ↦ by
    have := hg (g⁻¹ • τ) (σ.symm b)
    rw [AlgEquiv.apply_symm_apply, smul_inv_smul] at this
    exact this
  have hconjInv (δ : SL(2, ℝ)) : (ConjAct.toConjAct g)⁻¹ • δ = g⁻¹ * δ * g := by
    rw [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  have hconj : ConjAct.toConjAct g • S = S := by
    apply le_antisymm
    · intro δ hδ
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hconjInv] at hδ
      change ∀ τ b, ι ((g⁻¹ * δ * g) • τ) b = ι τ b at hδ
      intro τ b
      have e1 : δ • τ = g • ((g⁻¹ * δ * g) • (g⁻¹ • τ)) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
      rw [e1, ← hg, hδ, hg, smul_inv_smul]
    · intro δ hδ
      change ∀ τ b, ι (δ • τ) b = ι τ b at hδ
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hconjInv]
      intro τ b
      rw [mul_smul, mul_smul, hg', hδ, ← hg, AlgEquiv.apply_symm_apply]
  have hgS : g ∈ Subgroup.Commensurable.commensurator S := by
    simpa only [Subgroup.Commensurable.commensurator_mem_iff, hconj] using
      Subgroup.Commensurable.refl S
  -- `Γ`-invariance of `ι₀`
  have hΓ : ∀ γ ∈ Γ, ∀ (a : A) (τ : ℍ), ι₀ a (γ • τ) = ι₀ a τ := by
    intro γ hγ a τ
    have hπ : π ((γ • τ : ℍ) : ℂ) = π (τ : ℂ) := ((h.fibre τ (γ • τ)).mpr ⟨γ, hγ, rfl⟩).symm
    exact congrArg (fun χ : A →ₐ[ℂ] ℂ ↦ χ a)
      (hxy (pt ι₀ (γ • τ)) (pt ι₀ τ) (by simp [hx, hπ]) (by simp [hy, hπ]))
  -- `S ∩ Γ` has finite index in `Γ`
  set τ₀ := UpperHalfPlane.I
  haveI := finite_over (hloc τ₀)
  set R := Set.range fun ψ : Over B (pt ι₀ τ₀) ↦ (⇑ψ.1 : B → ℂ)
  haveI : Finite R := Set.finite_range _
  have hmemR : ∀ γ ∈ Γ, ι (γ⁻¹ • τ₀) ∈ R := by
    intro γ hγ
    obtain ⟨ψ, hψ⟩ := (hι.smul hΓ (Γ.inv_mem hγ)).pt τ₀
    exact ⟨ψ, hψ⟩
  have hSΓ : S.relIndex Γ ≠ 0 := by
    let f : Γ ⧸ S.subgroupOf Γ → R := Quotient.lift (fun γ : Γ ↦ ⟨ι ((γ : SL(2, ℝ))⁻¹ • τ₀),
      hmemR γ γ.2⟩) (by
        intro γ₁ γ₂ hγ
        have hS : (γ₁ : SL(2, ℝ))⁻¹ * γ₂ ∈ S := by
          have := (QuotientGroup.leftRel_apply).mp hγ
          exact Subgroup.mem_subgroupOf.mp this
        apply Subtype.ext
        funext b
        have := (S.inv_mem hS) ((γ₁ : SL(2, ℝ))⁻¹ • τ₀) b
        rw [← mul_smul, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one] at this
        exact this.symm)
    have hf : Function.Injective f := by
      intro q₁ q₂ hq
      induction q₁ using QuotientGroup.induction_on with
      | H γ₁ =>
      induction q₂ using QuotientGroup.induction_on with
      | H γ₂ =>
      have h1 : ι ((γ₁ : SL(2, ℝ))⁻¹ • τ₀) = ι ((γ₂ : SL(2, ℝ))⁻¹ • τ₀) :=
        congrArg Subtype.val hq
      have hl := (hι.smul hΓ (Γ.inv_mem γ₁.2)).eq hcov (hι.smul hΓ (Γ.inv_mem γ₂.2)) h1
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      intro τ b
      have := congrFun (congrFun hl ((γ₂ : SL(2, ℝ)) • τ)) b
      simp only [inv_smul_smul] at this
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
      exact this
    haveI : Finite (Γ ⧸ S.subgroupOf Γ) := Finite.of_injective f hf
    exact Subgroup.index_ne_zero_of_finite
  have hΓS : Γ.relIndex S ≠ 0 := fun h0 ↦
    IsUniformization.relIndex_closure_pmGroup_ne_zero G₁ G₂ (Subgroup.relIndex_eq_zero_of_le_right hSpm h0)
  have hcomm : Subgroup.Commensurable S Γ := ⟨hSΓ, hΓS⟩
  rwa [← Subgroup.Commensurable.eq hcomm]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
