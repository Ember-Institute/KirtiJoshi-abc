/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Anabelian/Genuine/Orbifold.lean
-/
import Pi1.Orbifold.Comparison
import TemperedFundamentalGroups.Setup.Orbifold
import Solutions.Source_ReferenceIutGenuinePi1

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open AffOrbicurve Pi1.Orbifold TemperedFundamentalGroups WeierstrassCurve
open JoshiTeich.ReferenceIut.Anabelian (Orbicurve)
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open scoped Classical

universe u

noncomputable section

section Transport

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

@[irreducible] private def galEquivOfEq {F F' : IntermediateField K Ω} (h : F = F') :
    (Ω ≃ₐ[F] Ω) ≃ₜ* (Ω ≃ₐ[F'] Ω) := by
  subst h
  exact ContinuousMulEquiv.refl _

private theorem galEquivOfEq_apply {F F' : IntermediateField K Ω} (h : F = F')
    (σ : Ω ≃ₐ[F] Ω) (x : Ω) : galEquivOfEq h σ x = σ x := by
  subst h
  with_unfolding_all rfl

private def galoisPi1EquivOfEq {F F' : IntermediateField K Ω} (h : F = F')
    [IsGalois F Ω] [IsGalois F' Ω]
    {H : Subgroup (Ω ≃ₐ[F] Ω)} {S : Set (Ω ≃ₐ[F] Ω)}
    (hH : IsClosed (H : Set (Ω ≃ₐ[F] Ω)))
    {H' : Subgroup (Ω ≃ₐ[F'] Ω)} {S' : Set (Ω ≃ₐ[F'] Ω)}
    (hH' : IsClosed (H' : Set (Ω ≃ₐ[F'] Ω)))
    (hHH : ∀ σ, σ ∈ H ↔ galEquivOfEq h σ ∈ H')
    (hSS : ∀ σ, σ ∈ S ↔ galEquivOfEq h σ ∈ S') :
    GaloisPi1.pi1 H S hH ≃ₜ* GaloisPi1.pi1 H' S' hH' := by
  subst h
  have sameAut : ∀ σ, galEquivOfEq (rfl : F = F) σ = σ := fun σ =>
    AlgEquiv.ext fun x => galEquivOfEq_apply rfl σ x
  simp only [sameAut] at hHH hSS
  obtain rfl : H = H' := Subgroup.ext hHH
  obtain rfl : S = S' := Set.ext hSS
  exact ContinuousMulEquiv.refl _

end Transport

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k)

private instance isGaloisOrbifoldBase : IsGalois (K₀ k (xG E)) (Ω E) := by
  change IsGalois (xLine E) (Ω E)
  rw [← baseField_eq_xLine E]
  infer_instance

private def modelGalEquiv : Gal E ≃ₜ* (Ω E ≃ₐ[K₀ k (xG E)] Ω E) :=
  galEquivOfEq (baseField_eq_xLine E)

private theorem modelGalEquiv_apply (σ : Gal E) (x : Ω E) : modelGalEquiv E σ x = σ x :=
  galEquivOfEq_apply (baseField_eq_xLine E) σ x

private def modelGalHom : (Ω E ≃ₐ[K₀ k (xG E)] Ω E) →* Gal E :=
  (modelGalEquiv E).symm.toMulEquiv.toMonoidHom

private theorem modelGalHom_modelGalEquiv (σ : Gal E) :
    modelGalHom E (modelGalEquiv E σ) = σ :=
  (modelGalEquiv E).symm_apply_apply σ

variable [E.IsElliptic]

private def modelGaloisData (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    GaloisData k (xG E) where
  H := (Hgp E ℓ M pm).comap (modelGalHom E)
  HL := (Hgp E ℓ M false).comap (modelGalHom E)
  le := Subgroup.comap_mono (Hgp_false_le E ℓ M pm)
  isOpen_HL := by
    rw [Subgroup.coe_comap]
    exact (isOpen_Hgp E ℓ M false).preimage (modelGalEquiv E).symm.continuous
  conj_mem h hh n hn := by
    change modelGalHom E (h * n * h⁻¹) ∈ Hgp E ℓ M false
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_Hgp_false E hh hn
  transcendental := transcendental_xG E

private theorem mem_modelGaloisData_H (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool)
    (σ : Gal E) : modelGalEquiv E σ ∈ (modelGaloisData E ℓ M pm).H ↔ σ ∈ Hgp E ℓ M pm := by
  change modelGalHom E (modelGalEquiv E σ) ∈ Hgp E ℓ M pm ↔ _
  rw [modelGalHom_modelGalEquiv]

private theorem mem_modelGaloisData_S (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool)
    (σ : Gal E) :
    modelGalEquiv E σ ∈ (modelGaloisData E ℓ M pm).S ↔
      σ ∈ baseValuationInertiaGenerators E := by
  have hHL : modelGalEquiv E σ ∈ (modelGaloisData E ℓ M pm).HL ↔ σ ∈ Hgp E ℓ M false := by
    change modelGalHom E (modelGalEquiv E σ) ∈ Hgp E ℓ M false ↔ _
    rw [modelGalHom_modelGalEquiv]
  have hInertia (W : ValuationSubring (Ω E)) :
      modelGalEquiv E σ ∈ GaloisPi1.inertia W ↔ valuationInertiaAt E σ W := by
    simp only [GaloisPi1.inertia, Set.mem_setOf_eq, valuationInertiaAt, modelGalEquiv_apply]
  rw [← unsignedValuationInertiaGenerators_eq_base E ℓ M]
  simp only [GaloisData.S, unsignedValuationInertiaGenerators, Set.mem_setOf_eq,
    hHL, mem_Hgp_false, hInertia]

private theorem modelConjugates_eq (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    GaloisPi1.conjSet (Hgp E ℓ M pm) (baseValuationInertiaGenerators E) =
      baseValuationInertiaGenerators E := by
  ext σ
  constructor
  · rintro ⟨g, -, s, hs, rfl⟩
    exact baseValuationInertiaGenerators_conj_mem E g s hs
  · intro hσ
    exact ⟨1, (Hgp E ℓ M pm).one_mem, σ, hσ, by simp⟩

private theorem modelGaloisKernel_eq_inertiaKernel
    (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    GaloisPi1.kernel (Hgp E ℓ M pm) (baseValuationInertiaGenerators E) = inertiaKernel E ℓ M pm := by
  rw [GaloisPi1.kernel, GaloisPi1.ambientKernel, modelConjugates_eq E, inertiaKernel,
    valuationInertiaSubgroup_eq_closure E]

private def quotientEquivOfEq {G : Type u} [Group G] [TopologicalSpace G]
    {N N' : Subgroup G} [N.Normal] [N'.Normal] (h : N = N') : (G ⧸ N) ≃ₜ* (G ⧸ N') := by
  subst h
  exact ContinuousMulEquiv.refl _

private def profiniteEquivOfEq {G H : ProfiniteGrp.{u}} (h : G = H) : G ≃ₜ* H := by
  subst h
  exact ContinuousMulEquiv.refl _

/-- The characteristic-zero model orbicurve at its generic geometric point. -/
def modelNormalizationOrbifold (X : Orbicurve k) : AffineOrbifold k :=
  let D := modelGaloisData X.E X.level X.M X.pm
  { R := D.R
    A := D.A
    Ω := Ω X.E }

/-- The étale fibre automorphism group of the model orbicurve is its valuation inertia quotient. -/
def modelEtalePi1Equiv (X : Orbicurve k) :
    (modelNormalizationOrbifold X).etalePi1 ≃ₜ* genuinePi1 X := by
  let D := modelGaloisData X.E X.level X.M X.pm
  let e := galoisPi1EquivOfEq (baseField_eq_xLine X.E)
    (isClosed_Hgp X.E X.level X.M X.pm) D.isClosed_H
    (fun σ => (mem_modelGaloisData_H X.E X.level X.M X.pm σ).symm)
    (fun σ => (mem_modelGaloisData_S X.E X.level X.M X.pm σ).symm)
  let q := quotientEquivOfEq (modelGaloisKernel_eq_inertiaKernel X.E X.level X.M X.pm)
  exact D.equivPi1.trans (e.symm.trans
    (q.trans (profiniteEquivOfEq (genuinePi1_eq_profiniteInertiaQuotient X).symm)))

end

end AbcAdaptation.Reference.Iut.Anabelian
