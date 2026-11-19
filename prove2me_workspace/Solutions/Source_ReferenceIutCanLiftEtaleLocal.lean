/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/EtalePoints.lean
-/
import Solutions.Source_ReferenceIutCanLiftEtalePoints
import Mathlib.Data.Finset.Prod
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.EtalePoints

open Polynomial
open scoped BigOperators

section Separate

variable {B : Type*} [CommRing B] [Algebra ℂ B]

/-- One step of separation: adding a generic multiple of a separator keeps the old separations. -/
theorem exists_separate_step {ι : Type*} [DecidableEq ι] (f : ι → B →ₐ[ℂ] ℂ) (T : Finset (ι × ι))
    {b s : B}
    (hb : ∀ p ∈ T, f p.1 b ≠ f p.2 b) {i j : ι} (hs : f i s ≠ f j s) :
    ∃ c : ℂ, ∀ p ∈ insert (i, j) T, f p.1 (b + c • s) ≠ f p.2 (b + c • s) := by
  classical
  set sol : ι × ι → ℂ := fun p ↦ -(f p.1 b - f p.2 b) / (f p.1 s - f p.2 s)
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ((insert (i, j) T).image sol)
  refine ⟨c, fun p hp h ↦ hc (Finset.mem_image.mpr ⟨p, hp, ?_⟩)⟩
  simp only [map_add, map_smul, smul_eq_mul] at h
  have hslope : f p.1 s - f p.2 s ≠ 0 := by
    intro h0
    have hconst : f p.1 b = f p.2 b := by
      have : f p.1 b - f p.2 b + c * (f p.1 s - f p.2 s) = 0 := by linear_combination h
      rw [h0, mul_zero, add_zero, sub_eq_zero] at this; exact this
    rcases Finset.mem_insert.mp hp with rfl | hpT
    · exact hs (sub_eq_zero.mp h0)
    · exact hb p hpT hconst
  simp only [sol]
  field_simp
  linear_combination -h

/-- **Separating element**: finitely many distinct `ℂ`-points of `B` are separated by one
element. -/
theorem exists_separating {ι : Type*} [Finite ι] (f : ι → B →ₐ[ℂ] ℂ)
    (hf : Function.Injective f) : ∃ b : B, Function.Injective fun i ↦ f i b := by
  classical
  haveI := Fintype.ofFinite ι
  have hsep : ∀ p : ι × ι, p.1 ≠ p.2 → ∃ s : B, f p.1 s ≠ f p.2 s := fun p hp ↦ by
    by_contra h
    push Not at h
    exact hp (hf (AlgHom.ext h))
  have key : ∀ T : Finset (ι × ι), (∀ p ∈ T, p.1 ≠ p.2) →
      ∃ b : B, ∀ p ∈ T, f p.1 b ≠ f p.2 b := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨0, by simp⟩
    | insert p T hp ih =>
      intro hT
      obtain ⟨b, hb⟩ := ih fun q hq ↦ hT q (Finset.mem_insert_of_mem hq)
      obtain ⟨s, hs⟩ := hsep p (hT p (Finset.mem_insert_self _ _))
      obtain ⟨c, hc⟩ := exists_separate_step f T hb (i := p.1) (j := p.2) hs
      exact ⟨b + c • s, by simpa using hc⟩
  obtain ⟨b, hb⟩ := key (Finset.univ.offDiag) fun p hp ↦ (Finset.mem_offDiag.mp hp).2.2
  refine ⟨b, fun i j hij ↦ ?_⟩
  by_contra hne
  exact hb (i, j) (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩) hij

end Separate

section LocPres

variable {A B : Type*} [CommRing A] [IsDomain A] [Algebra ℂ A]
  [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B] [Algebra A B]
  [IsScalarTower ℂ A B]

omit [IsDomain B] [Algebra ℂ A] [Algebra ℂ B] [Algebra.FiniteType ℂ B] [IsScalarTower ℂ A B] in
/-- In an unramified extension of Dedekind domains, `𝔭 B` is the intersection of the primes
over `𝔭`. -/
theorem mem_map_of_forall_mem [IsDedekindDomain B] [FaithfulSMul A B] {p : Ideal A}
    [p.IsMaximal] (hp : p ≠ ⊥) (het : ∀ w : Ideal B, w.IsMaximal → w.ramificationIdx A = 1)
    {b : B} (hb : ∀ q ∈ p.primesOver B, b ∈ q) : b ∈ p.map (algebraMap A B) := by
  classical
  set J := p.map (algebraMap A B)
  have hJ : J ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  have hprod : J = ∏ q ∈ (UniqueFactorizationMonoid.factors J).toFinset, q := by
    have h1 := UniqueFactorizationMonoid.factors_prod hJ
    rw [associated_iff_eq] at h1
    conv_lhs => rw [← h1]
    rw [Finset.prod_multiset_count]
    refine Finset.prod_congr rfl fun q hq ↦ ?_
    have hprime : q.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_factor q
      (Multiset.mem_toFinset.mp hq))
    have hle : J ≤ q := Ideal.le_of_dvd
      (UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hq))
    have hqne : q ≠ ⊥ := ne_bot_of_le_ne_bot hJ hle
    haveI hqmax : q.IsMaximal := hprime.isMaximal hqne
    haveI : q.LiesOver p := ⟨(Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _
      hqmax.ne_top) (Ideal.map_le_iff_le_comap.mp hle))⟩
    have hc := Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count p q hJ
    rw [het q hqmax] at hc
    rw [← hc, pow_one]
  rw [hprod, Ideal.prod_eq_iInf_of_pairwise_isCoprime ?_]
  · refine Submodule.mem_iInf _ |>.mpr fun q ↦ Submodule.mem_iInf _ |>.mpr fun hq ↦ ?_
    have hle : J ≤ q := Ideal.le_of_dvd
      (UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hq))
    have hprime : q.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_factor q
      (Multiset.mem_toFinset.mp hq))
    have hqne : q ≠ ⊥ := ne_bot_of_le_ne_bot hJ hle
    haveI hqmax : q.IsMaximal := hprime.isMaximal hqne
    refine hb q ⟨hprime, ⟨(Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _
      hqmax.ne_top) (Ideal.map_le_iff_le_comap.mp hle))⟩⟩
  · intro q hq q' hq' hne
    simp only [Finset.mem_coe] at hq hq'
    have hm : ∀ r ∈ (UniqueFactorizationMonoid.factors J).toFinset, r.IsMaximal := fun r hr ↦
      (Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_factor r
        (Multiset.mem_toFinset.mp hr))).isMaximal (ne_bot_of_le_ne_bot hJ
          (Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors
            (Multiset.mem_toFinset.mp hr))))
    exact (Ideal.isCoprime_iff_sup_eq).mpr ((hm q hq).coprime_of_ne (hm q' hq') hne)

attribute [local instance] FractionRing.liftAlgebra

omit [IsDomain B] in
/-- **Local presentation** of an unramified finite extension at a point `χ` of `A`. -/
theorem exists_locPres [Algebra.FiniteType ℂ A] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.Flat A B] [FaithfulSMul A B] (hA : ¬ IsField A)
    (het : ∀ w : Ideal B, w.IsMaximal → w.ramificationIdx A = 1) (χ : A →ₐ[ℂ] ℂ) :
    ∃ (b₀ : B) (F : A[X]) (δ : A), F.Monic ∧ F.natDegree = Module.finrank A B ∧
      aeval b₀ F = 0 ∧ χ δ ≠ 0 ∧ ∀ b : B, algebraMap A B δ * b ∈ Algebra.adjoin A {b₀} := by
  classical
  set n := Module.finrank A B
  set p := RingHom.ker χ
  haveI hp : p.IsMaximal := ker_isMaximal χ
  have hp0 : p ≠ ⊥ := fun h ↦ hA (Ring.isField_iff_maximal_bot.mpr (h ▸ hp))
  -- the points over `χ`
  have hcard := card_points_over het χ
  haveI : Finite (PtOver B χ) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    rw [Nat.card_eq_zero_of_infinite] at hcard
    have : 0 < n := Module.finrank_pos
    omega
  haveI : Fintype (PtOver B χ) := Fintype.ofFinite _
  obtain ⟨b₀, hb₀⟩ := exists_separating (fun ψ : PtOver B χ ↦ ψ.1) Subtype.val_injective
  -- the minimal polynomial
  have hint : IsIntegral A b₀ := Algebra.IsIntegral.isIntegral b₀
  set F := minpoly A b₀
  have hFm : F.Monic := minpoly.monic hint
  have hFb : aeval b₀ F = 0 := minpoly.aeval A b₀
  have hroot : ∀ ψ : PtOver B χ, (F.map (χ : A →+* ℂ)).IsRoot (ψ.1 b₀) := by
    intro ψ
    have h1 := congrArg ψ.1 hFb
    have h2 := Polynomial.hom_eval₂ F (algebraMap A B) (ψ.1 : B →+* ℂ) b₀
    rw [RingHom.coe_coe] at h2
    rw [aeval_def, map_zero, h2] at h1
    rw [IsRoot, eval_map]
    convert h1 using 2
    ext a; simp [ψ.2]
  have hge : n ≤ F.natDegree := by
    have hmaps : ∀ ψ : PtOver B χ, ψ.1 b₀ ∈ (F.map (χ : A →+* ℂ)).roots.toFinset := fun ψ ↦ by
      rw [Multiset.mem_toFinset, mem_roots ((hFm.map _).ne_zero)]; exact hroot ψ
    have := Nat.card_le_card_of_injective (fun ψ : PtOver B χ ↦
      (⟨ψ.1 b₀, hmaps ψ⟩ : (F.map (χ : A →+* ℂ)).roots.toFinset))
      fun ψ ψ' h ↦ hb₀ (congrArg Subtype.val h)
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_coe] at this
    calc n ≤ _ := this
      _ ≤ Multiset.card (F.map (χ : A →+* ℂ)).roots := Multiset.toFinset_card_le _
      _ ≤ (F.map (χ : A →+* ℂ)).natDegree := card_roots' _
      _ = F.natDegree := hFm.natDegree_map _
  have hle : F.natDegree ≤ n := by
    haveI : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
    haveI : FiniteDimensional (FractionRing A) (FractionRing B) :=
      Module.Finite.of_isLocalization A B (nonZeroDivisors A)
    have h1 := minpoly.isIntegrallyClosed_eq_field_fractions (FractionRing A) (FractionRing B)
      hint
    have h2 := minpoly.natDegree_le (A := FractionRing A) (algebraMap B (FractionRing B) b₀)
    rw [h1, hFm.natDegree_map] at h2
    rwa [IsFractionRing.finrank_eq A (FractionRing A) B (FractionRing B)] at h2
  -- `B = A[b₀] + 𝔭 B`, by Lagrange interpolation
  set N : Submodule A B := Subalgebra.toSubmodule (Algebra.adjoin A {b₀})
  have hspan : ∀ b : B, ∃ c ∈ N, b - c ∈ p.map (algebraMap A B) := by
    intro b
    set P := Lagrange.interpolate (Finset.univ : Finset (PtOver B χ)) (fun ψ ↦ ψ.1 b₀)
      (fun ψ ↦ ψ.1 b)
    set c := aeval b₀ (P.map (algebraMap ℂ A))
    refine ⟨c, ?_, ?_⟩
    · change c ∈ Algebra.adjoin A {b₀}
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨_, rfl⟩
    refine mem_map_of_forall_mem hp0 het fun q hq ↦ ?_
    haveI : q.IsMaximal := by
      haveI := hq.1; haveI := hq.2; exact Ideal.IsMaximal.of_liesOver_isMaximal q p
    obtain ⟨ψ, hψ⟩ := exists_point_of_isMaximal q
    have hψχ : ∀ a, ψ (algebraMap A B a) = χ a := by
      have h1 : RingHom.ker (ψ.comp (IsScalarTower.toAlgHom ℂ A B)) = RingHom.ker χ := by
        ext a
        have hover' : p = q.under A := hq.2.over
        have hq' : algebraMap A B a ∈ q ↔ a ∈ p :=
          Ideal.mem_comap.symm.trans (Ideal.ext_iff.mp hover' a).symm
        simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply,
          IsScalarTower.coe_toAlgHom']
        rw [← RingHom.mem_ker, ← AlgHom.coe_toRingHom, hψ, hq']; rfl
      exact fun a ↦ congrFun (congrArg DFunLike.coe (point_ext_of_ker h1)) a
    rw [← hψ, RingHom.mem_ker, map_sub, sub_eq_zero]
    have hc : ψ c = P.eval (ψ b₀) := by
      simp only [c, aeval_map_algebraMap]
      rw [← Polynomial.aeval_algHom_apply, coe_aeval_eq_eval]
    rw [hc]
    exact (Lagrange.eval_interpolate_at_node (fun ψ : PtOver B χ ↦ ψ.1 b)
      (fun ψ _ ψ' _ h ↦ hb₀ h)
      (Finset.mem_univ ⟨ψ, hψχ⟩)).symm
  -- Nakayama
  have hfg : (⊤ : Submodule A (B ⧸ N)).FG := Module.Finite.fg_top
  have hle' : (⊤ : Submodule A (B ⧸ N)) ≤ p • ⊤ := by
    rintro x -
    obtain ⟨b, rfl⟩ := N.mkQ_surjective x
    obtain ⟨c, hc, hbc⟩ := hspan b
    have : N.mkQ b = N.mkQ (b - c) := by
      rw [map_sub, Submodule.mkQ_apply N c, (Submodule.Quotient.mk_eq_zero N).mpr hc, sub_zero]
    rw [this]
    have hmem : b - c ∈ (p • ⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]; exact hbc
    have := Submodule.mem_map_of_mem (f := N.mkQ) hmem
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
    exact this
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p ⊤ hfg hle'
  refine ⟨b₀, F, r, hFm, le_antisymm hle hge, hFb, ?_, fun b ↦ ?_⟩
  · have : χ (r - 1) = 0 := hr1
    rw [map_sub, map_one, sub_eq_zero] at this
    rw [this]; exact one_ne_zero
  · have := hr (N.mkQ b) trivial
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Algebra.smul_def] at this
    exact this

end LocPres


end AbcAdaptation.Reference.Iut.Anabelian.EtalePoints
