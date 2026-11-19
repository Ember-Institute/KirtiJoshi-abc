/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/EtalePoints.lean
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.RamificationInertia.Basic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.EtalePoints

open scoped BigOperators

section Points

variable {R : Type*} [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R]

/-- **Nullstellensatz**: a maximal ideal of a finitely generated `ℂ`-algebra is the kernel of a
`ℂ`-point. -/
theorem exists_point_of_isMaximal (w : Ideal R) [hw : w.IsMaximal] :
    ∃ ψ : R →ₐ[ℂ] ℂ, RingHom.ker ψ = w := by
  letI : Field (R ⧸ w) := Ideal.Quotient.field w
  haveI : Algebra.FiniteType ℂ (R ⧸ w) := Algebra.FiniteType.trans (S := R) inferInstance
    inferInstance
  haveI : Module.Finite ℂ (R ⧸ w) := finite_of_finite_type_of_isJacobsonRing ℂ (R ⧸ w)
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := R ⧸ w)
  set e : ℂ ≃ₐ[ℂ] (R ⧸ w) := AlgEquiv.ofBijective (Algebra.ofId ℂ (R ⧸ w)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ w), ?_⟩
  ext r
  simp [Ideal.Quotient.eq_zero_iff_mem]

omit [Algebra.FiniteType ℂ R] in
theorem ker_isMaximal (ψ : R →ₐ[ℂ] ℂ) : (RingHom.ker ψ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap ℂ R c, by simp⟩

omit [Algebra.FiniteType ℂ R] in
theorem point_ext_of_ker {ψ ψ' : R →ₐ[ℂ] ℂ} (h : RingHom.ker ψ = RingHom.ker ψ') : ψ = ψ' := by
  ext r
  have : r - algebraMap ℂ R (ψ r) ∈ RingHom.ker ψ := by simp
  rw [h, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
  exact this.symm

end Points

section Count

variable {A B : Type*} [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
  [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B] [Algebra A B]
  [IsScalarTower ℂ A B]

/-- Points of `B` over a point `χ` of `A`. -/
abbrev PtOver (B : Type*) [CommRing B] [Algebra ℂ B] [Algebra A B] (χ : A →ₐ[ℂ] ℂ) : Type _ :=
  {ψ : B →ₐ[ℂ] ℂ // ∀ a, ψ (algebraMap A B a) = χ a}

omit [IsDomain B] in
/-- The residue field of a maximal ideal of a finitely generated `ℂ`-algebra is `ℂ`. -/
theorem surjective_algebraMap_residueField (q : Ideal B) [q.IsMaximal] :
    Function.Surjective (algebraMap ℂ q.ResidueField) := by
  letI : Field (B ⧸ q) := Ideal.Quotient.field q
  haveI : Algebra.FiniteType ℂ (B ⧸ q) := Algebra.FiniteType.trans (S := B) inferInstance
    inferInstance
  haveI : Module.Finite ℂ (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ q)
  have h1 := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := B ⧸ q)).2
  have h2 := (q.bijective_algebraMap_quotient_residueField).2
  intro z
  obtain ⟨y, rfl⟩ := h2 z
  obtain ⟨c, rfl⟩ := h1 y
  exact ⟨c, by rw [IsScalarTower.algebraMap_apply ℂ (B ⧸ q) q.ResidueField]⟩

variable [Module.Finite A B] [Module.Flat A B]

omit [IsDomain A] [Algebra.FiniteType ℂ A] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
  [IsScalarTower ℂ A B] [Module.Flat A B] in
theorem isMaximal_of_mem_primesOver (χ : A →ₐ[ℂ] ℂ) {q : Ideal B}
    (hq : q ∈ (RingHom.ker χ).primesOver B) : q.IsMaximal := by
  haveI := ker_isMaximal χ
  haveI := hq.1; haveI := hq.2
  exact Ideal.IsMaximal.of_liesOver_isMaximal q (RingHom.ker χ)

omit [Algebra.FiniteType ℂ A] [IsDomain B] [Module.Finite A B] [Module.Flat A B] in
/-- Points of `B` over `χ` are the primes of `B` over `ker χ`. -/
noncomputable def ptOverEquiv (χ : A →ₐ[ℂ] ℂ) : PtOver B χ ≃ (RingHom.ker χ).primesOver B := by
  classical
  set p := RingHom.ker χ
  haveI hp : p.IsMaximal := ker_isMaximal χ
  have hover : ∀ ψ : PtOver B χ, RingHom.ker ψ.1 ∈ p.primesOver B := fun ψ ↦ by
    haveI := ker_isMaximal ψ.1
    refine ⟨Ideal.IsMaximal.isPrime inferInstance, ⟨?_⟩⟩
    ext a
    simp [p, RingHom.mem_ker, Ideal.mem_comap, ψ.2]
  refine Equiv.ofBijective (fun ψ ↦ ⟨RingHom.ker ψ.1, hover ψ⟩) ⟨fun ψ ψ' h ↦ ?_, fun q ↦ ?_⟩
  · exact Subtype.ext (point_ext_of_ker (congrArg Subtype.val h))
  · haveI := isMaximal_of_mem_primesOver χ q.2
    obtain ⟨ψ, hψ⟩ := exists_point_of_isMaximal q.1
    refine ⟨⟨ψ, fun a ↦ ?_⟩, Subtype.ext hψ⟩
    have h1 : RingHom.ker (ψ.comp (IsScalarTower.toAlgHom ℂ A B)) = RingHom.ker χ := by
      ext a
      have hover' : p = q.1.under A := q.2.2.over
      have hq : algebraMap A B a ∈ q.1 ↔ a ∈ p := by
        exact Ideal.mem_comap.symm.trans (Ideal.ext_iff.mp hover' a).symm
      have hk : ψ (algebraMap A B a) = 0 ↔ algebraMap A B a ∈ q.1 := by
        rw [← hψ, RingHom.mem_ker]
      simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply,
        IsScalarTower.coe_toAlgHom']
      rw [hk, hq]; rfl
    exact congrFun (congrArg DFunLike.coe (point_ext_of_ker h1)) a

omit [Algebra.FiniteType ℂ A] [IsDomain B] in
/-- **`Σ e = n`** over a point of `A` (all residue fields are `ℂ`). -/
theorem sum_ramificationIdx (χ : A →ₐ[ℂ] ℂ) [Fintype ((RingHom.ker χ).primesOver B)] :
    ∑ q : (RingHom.ker χ).primesOver B, q.1.ramificationIdx A = Module.finrank A B := by
  classical
  haveI hp : (RingHom.ker χ).IsMaximal := ker_isMaximal χ
  rw [← Ideal.sum_ramification_inertia_eq_finrank (RingHom.ker χ) B]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  haveI := isMaximal_of_mem_primesOver χ q.2
  haveI := q.2.1
  -- inertia degree `1`
  letI := Localization.AtPrime.algebraOfLiesOver (q.1.under A) q.1
  rw [Ideal.inertiaDeg_def]
  have : Module.finrank (q.1.under A).ResidueField q.1.ResidueField = 1 := by
    rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
    refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨c, rfl⟩ := surjective_algebraMap_residueField q.1 z
    rw [IsScalarTower.algebraMap_apply ℂ (q.1.under A).ResidueField q.1.ResidueField]
    exact Subalgebra.algebraMap_mem _ _
  rw [this, mul_one]

omit [Algebra.FiniteType ℂ A] [IsDomain B] in
/-- **Exactly `n` points over every point**, for an unramified extension. -/
theorem card_points_over (het : ∀ w : Ideal B, w.IsMaximal → w.ramificationIdx A = 1)
    (χ : A →ₐ[ℂ] ℂ) : Nat.card (PtOver B χ) = Module.finrank A B := by
  classical
  haveI : Fintype ((RingHom.ker χ).primesOver B) :=
    (Algebra.QuasiFinite.finite_primesOver (RingHom.ker χ) (S := B)).fintype
  rw [Nat.card_congr (ptOverEquiv χ), Nat.card_eq_fintype_card, ← sum_ramificationIdx χ,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [het q.1 (isMaximal_of_mem_primesOver χ q.2)]

end Count


end AbcAdaptation.Reference.Iut.Anabelian.EtalePoints
