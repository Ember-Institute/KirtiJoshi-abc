/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/FEtTransitive.lean
-/
import Solutions.Source_ReferenceIutCanLiftAnalyticLiftFacts

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped BigOperators MatrixGroups

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  {ι₀ : A →ₐ[ℂ] (ℍ → ℂ)}

variable [IsDomain B] [Algebra.IsIntegral A B]

/-- **Transitivity**: every lift is a `Γ`-translate of a given holomorphic lift. -/
theorem exists_smul_eq (hhol : ∀ a, HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    {Γ : Subgroup SL(2, ℝ)} (hΓ : ∀ γ ∈ Γ, ∀ a τ, ι₀ a (γ • τ) = ι₀ a τ) {h₀ : ℍ → ℂ}
    (hgrowth : ∀ a, PolyBdd h₀ fun τ ↦ ‖ι₀ a τ‖)
    (hpoly : ∀ g : ℍ → ℂ, HolH g → (∀ γ ∈ Γ, ∀ τ, g (γ • τ) = g τ) →
      PolyBdd h₀ (fun τ ↦ ‖g τ‖) → ∃ a, ∀ τ, ι₀ a τ = g τ)
    (hinj : Function.Injective ι₀) {ι ι' : ℍ → B → ℂ} (hι : IsLift ι₀ ι)
    (hιh : ∀ b, HolH fun τ ↦ ι τ b) (hι' : IsLift ι₀ ι') :
    ∃ γ ∈ Γ, ι' = fun τ ↦ ι (γ • τ) := by
  classical
  haveI : Nontrivial A := ⟨⟨1, 0, fun h ↦ by
    have := congrFun (congrArg ι₀ h) UpperHalfPlane.I; simp at this⟩⟩
  have hcov := isCoveringMap_proj hhol hcount hloc
  set τ₀ := UpperHalfPlane.I
  obtain ⟨b₀, F, δ, hFm, hFn, hF, hδ, hpres⟩ := hloc τ₀
  -- the orbit
  set O : Set (ℍ → B → ℂ) := {f | ∃ γ ∈ Γ, f = fun τ ↦ ι (γ • τ)}
  have hOlift : ∀ f ∈ O, IsLift ι₀ f := by
    rintro f ⟨γ, hγ, rfl⟩; exact hι.smul hΓ hγ
  have hOhol : ∀ f ∈ O, ∀ b, HolH fun τ ↦ f τ b := by
    rintro f ⟨γ, hγ, rfl⟩ b; exact (hιh b).comp_smul γ
  have hιO : ι ∈ O := ⟨1, Γ.one_mem, by simp⟩
  -- the points over `τ₀`
  have hOverinj : Function.Injective fun ψ : Over B (pt ι₀ τ₀) ↦ ψ.1 b₀ :=
    fun ψ ψ' h ↦ Over.ext_of_apply_eq hδ hpres h
  haveI hOverfin : Finite (Over B (pt ι₀ τ₀)) := by
    have hmaps : ∀ ψ : Over B (pt ι₀ τ₀),
        ψ.1 b₀ ∈ (F.map (pt ι₀ τ₀ : A →+* ℂ)).roots.toFinset := fun ψ ↦ by
      rw [Multiset.mem_toFinset, mem_roots ((hFm.map _).ne_zero)]; exact ψ.isRoot hF
    exact Finite.of_injective (fun ψ ↦ (⟨ψ.1 b₀, hmaps ψ⟩ :
      (F.map (pt ι₀ τ₀ : A →+* ℂ)).roots.toFinset))
      fun ψ ψ' h ↦ hOverinj (congrArg Subtype.val h)
  -- the orbit is finite
  choose ψf hψf using fun f : {f // f ∈ O} ↦ (hOlift f.1 f.2).pt τ₀
  have hψfinj : Function.Injective ψf := fun f g h ↦ Subtype.ext
    ((hOlift f.1 f.2).eq hcov (hOlift g.1 g.2) (by rw [← hψf, ← hψf, h]))
  haveI : Finite {f // f ∈ O} := Finite.of_injective ψf hψfinj
  have hOfin : O.Finite := Set.toFinite O
  set S := hOfin.toFinset
  have hS : ∀ f, f ∈ S ↔ f ∈ O := fun f ↦ Set.Finite.mem_toFinset hOfin
  set m := S.card
  -- the polynomial
  set P : ℍ → ℂ[X] := fun τ ↦ ∏ f ∈ S, (X - C (f τ b₀))
  have hPinv : ∀ γ ∈ Γ, ∀ τ, P (γ • τ) = P τ := by
    intro γ hγ τ
    refine Finset.prod_nbij' (fun f τ ↦ f (γ • τ)) (fun f τ ↦ f (γ⁻¹ • τ)) ?_ ?_ ?_ ?_ ?_
    · intro f hf
      obtain ⟨γ', hγ', rfl⟩ := (hS f).mp hf
      exact (hS _).mpr ⟨γ' * γ, Γ.mul_mem hγ' hγ, by funext τ; simp [mul_smul]⟩
    · intro f hf
      obtain ⟨γ', hγ', rfl⟩ := (hS f).mp hf
      exact (hS _).mpr ⟨γ' * γ⁻¹, Γ.mul_mem hγ' (Γ.inv_mem hγ), by funext τ; simp [mul_smul]⟩
    · intro f _; funext τ; simp
    · intro f _; funext τ; simp
    · intro f _; rfl
  have hPm : ∀ τ, (P τ).Monic := fun τ ↦ monic_prod_X_sub_C _ _
  have hPdeg : ∀ τ, (P τ).natDegree = m := fun τ ↦ natDegree_finsetProd_X_sub_C_eq_card _ _
  -- the root bound
  set R : ℍ → ℝ := fun τ ↦ 1 + ∑ i ∈ Finset.range n, ‖ι₀ (F.coeff i) τ‖
  have hR : PolyBdd h₀ R := (PolyBdd.const 1).add (PolyBdd.sum _ fun i _ ↦ hgrowth _)
  have hfR : ∀ f ∈ S, ∀ τ, ‖f τ b₀‖ ≤ R τ := by
    intro f hf τ
    obtain ⟨ψ, hψ⟩ := (hOlift f ((hS f).mp hf)).pt τ
    have := norm_le_of_isRoot_monic (hFm.map (pt ι₀ τ : A →+* ℂ)) (ψ.isRoot hF)
    rw [(hFm.natDegree_map _), hFn] at this
    simp only [coeff_map, RingHom.coe_coe, pt_apply] at this
    rw [← hψ]; exact this
  -- the coefficients lie in `ι₀(A)`
  have hcoeff : ∀ k, ∃ a : A, ∀ τ, ι₀ a τ = (P τ).coeff k := by
    intro k
    refine hpoly _ ?_ (fun γ hγ τ ↦ by rw [hPinv γ hγ τ]) ?_
    · exact differentiableOn_coeff_prod_X_sub_C S (a := fun f z ↦ f (ofComplex z) b₀)
        (fun f hf ↦ hOhol f ((hS f).mp hf) b₀) k
    · refine (PolyBdd.prod S (u := fun _ τ ↦ 1 + R τ) (fun _ _ ↦ (PolyBdd.const 1).add hR)
        fun _ _ τ ↦ by positivity).mono fun τ ↦ ?_
      refine (norm_coeff_prod_X_sub_C_le _ _ k).trans ?_
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity) fun f hf ↦ by linarith [hfR f hf τ]
  choose a ha using hcoeff
  set Q : A[X] := X ^ m + ∑ i : Fin m, C (a i) * X ^ (i : ℕ)
  have hQm : Q.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hQmap : ∀ τ, Q.map (pt ι₀ τ : A →+* ℂ) = P τ := by
    intro τ
    conv_rhs => rw [(hPm τ).as_sum, hPdeg τ, Finset.sum_range]
    simp only [Q, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C, RingHom.coe_coe, pt_apply, ha]
  have hQb : aeval b₀ Q = 0 := by
    refine hι.eq_zero hinj fun τ ↦ ?_
    obtain ⟨ψ, hψ⟩ := hι.pt τ
    rw [← hψ, Over.apply_aeval, hQmap]
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero ((hS ι).mpr hιO) (by rw [hψ, sub_self])
  -- counting at `τ₀`
  have hnm : n ≤ m := by
    have hroots : ∀ ψ : Over B (pt ι₀ τ₀),
        ψ.1 b₀ ∈ (Q.map (pt ι₀ τ₀ : A →+* ℂ)).roots.toFinset := fun ψ ↦ by
      rw [Multiset.mem_toFinset, mem_roots ((hQm.map _).ne_zero), IsRoot, ← Over.apply_aeval,
        hQb, map_zero]
    have h1 := Nat.card_le_card_of_injective (fun ψ : Over B (pt ι₀ τ₀) ↦
      (⟨ψ.1 b₀, hroots ψ⟩ : (Q.map (pt ι₀ τ₀ : A →+* ℂ)).roots.toFinset))
      fun ψ ψ' h ↦ hOverinj (congrArg Subtype.val h)
    rw [hcount, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
    calc n ≤ _ := h1
      _ ≤ Multiset.card (Q.map (pt ι₀ τ₀ : A →+* ℂ)).roots := Multiset.toFinset_card_le _
      _ ≤ (Q.map (pt ι₀ τ₀ : A →+* ℂ)).natDegree := card_roots' _
      _ = m := by
        rw [hQm.natDegree_map]
        change (X ^ m + ∑ i : Fin m, C (a i) * X ^ (i : ℕ)).natDegree = m
        rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
        exact (degree_sum_fin_lt _).trans_eq (degree_X_pow m).symm
  have hmO : m = Nat.card {f // f ∈ O} := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card O hOfin]
  have hbij := hψfinj.bijective_of_nat_card_le (by rw [hcount, ← hmO]; exact hnm)
  obtain ⟨ψ', hψ'⟩ := hι'.pt τ₀
  obtain ⟨f, hf⟩ := hbij.2 ψ'
  have hfeq : f.1 = ι' := (hOlift f.1 f.2).eq hcov hι' (by rw [← hψf, hf, hψ'])
  obtain ⟨γ, hγ, hfγ⟩ := f.2
  exact ⟨γ, hγ, hfeq.symm.trans hfγ⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
