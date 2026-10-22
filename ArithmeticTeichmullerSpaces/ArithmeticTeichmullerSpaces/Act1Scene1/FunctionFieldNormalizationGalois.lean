/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbicurve/SubfieldGalois.lean`
original-author: Christian Merten <lana@merten.dev> (Git author; no author header)
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `1314bc8d47c13db19b895144391571f1ac5ecfab`
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f` (pi1 package)
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the package LICENSE before copying. The source has no
copyright header and the package has no NOTICE file. Retain the license text.
modifications: use the local normalization rings and actual inclusion algebras.
Expose the actual automorphism action and split the field and ring Galois proofs.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationFinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Pi1/Orbicurve/SubfieldGalois.lean, isGaloisGroup_fixSub.
fidelity: for an actual finite Galois extension N/k(t), the actual subgroup
fixing F acts as a Galois group on the actual normalization rings for F and N.
boundary: Scene1/Derived. This proves the algebraic Galois input to the inertia
and ramification comparison; no covering law is assumed.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open IntermediateField
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
universe u
noncomputable section
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
variable (N : IntermediateField (rationalBase k t) Ω)

/-- The subgroup `Gal(N / F)` of `Gal(N / K₀)` (the elements fixing `F ∩ N`). -/
def fixSub (F : IntermediateField (rationalBase k t) Ω) : Subgroup (N ≃ₐ[rationalBase k t] N) where
  carrier := {σ | ∀ x : N, (x : Ω) ∈ F → σ x = x}
  one_mem' _ _ := rfl
  mul_mem' {σ τ} hσ hτ x hx := by
    rw [AlgEquiv.mul_apply, hτ x hx, hσ x hx]
  inv_mem' {σ} hσ x hx := by
    rw [← hσ x hx]
    conv_lhs => rw [← hσ x hx]
    simp

variable {N}

lemma mem_fixSub {F : IntermediateField (rationalBase k t) Ω} {σ : N ≃ₐ[rationalBase k t] N} :
    σ ∈ fixSub N F ↔ ∀ x : N, (x : Ω) ∈ F → σ x = x := Iff.rfl

lemma fixSub_antitone {F L : IntermediateField (rationalBase k t) Ω} (h : F ≤ L) :
    fixSub N L ≤ fixSub N F := fun _ hσ x hx => hσ x (h hx)

variable {F : IntermediateField (rationalBase k t) Ω} (hFN : F ≤ N)

lemma fixSub_eq_fixingSubgroup :
    fixSub N F = (IntermediateField.restrict hFN).fixingSubgroup := by
  ext σ
  rw [mem_fixSub, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact h x ((IntermediateField.mem_restrict hFN x).mp hx)
  · intro h x hx
    exact h x ((IntermediateField.mem_restrict hFN x).mpr hx)


/-- The actual field inclusion as an algebra structure. -/
abbrev fieldInclusionAlgebra (hFN : F ≤ N) : Algebra F N :=
  (IntermediateField.inclusion hFN).toAlgebra

lemma fixSub_eq_fixingSubgroup_range :
    letI := fieldInclusionAlgebra hFN
    fixSub N F = _root_.fixingSubgroup (N ≃ₐ[rationalBase k t] N)
      (Set.range (algebraMap F N)) := by
  letI := fieldInclusionAlgebra hFN
  ext σ
  rw [mem_fixSub, mem_fixingSubgroup_iff]
  constructor
  · rintro h _ ⟨x, rfl⟩
    exact h _ x.2
  · intro h x hx
    exact h x ⟨⟨x, hx⟩, rfl⟩

local instance galoisNormalizationCoeffComm :
    SMulCommClass (N ≃ₐ[rationalBase k t] N) (polynomialBase k t) N where
  smul_comm τ a b := by
    change τ (algebraMap (polynomialBase k t) N a * b) =
      algebraMap (polynomialBase k t) N a * τ b
    rw [map_mul, show τ (algebraMap (polynomialBase k t) N a) =
      algebraMap (polynomialBase k t) N a from
        τ.commutes (algebraMap (polynomialBase k t) (rationalBase k t) a)]

/-- The standard field-automorphism action restricted to the actual integral closure. -/
@[instance_reducible] def fieldRingAction :
    MulSemiringAction (N ≃ₐ[rationalBase k t] N) (coordRing t N) := inferInstance

attribute [local instance] fieldRingAction

variable [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N]

/-- The actual fixing subgroup is the relative Galois group of the field inclusion. -/
theorem fieldGaloisGroup_fixSub :
    letI := fieldInclusionAlgebra hFN
    IsGaloisGroup (fixSub N F) F N := by
  letI := fieldInclusionAlgebra hFN
  have : FaithfulSMul F N :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IntermediateField.inclusion hFN).injective
  have : IsScalarTower (rationalBase k t) F N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [fixSub_eq_fixingSubgroup_range hFN]
  exact IsGaloisGroup.of_isScalarTower (N ≃ₐ[rationalBase k t] N) (rationalBase k t) N F

/-- The same fixing subgroup acts as a Galois group of the normalization inclusion. -/
theorem normalizationGaloisGroup_fixSub (ht : Transcendental k t) :
    letI := ringMapAlgebra hFN
    IsGaloisGroup (fixSub N F) (coordRing t F) (coordRing t N) := by
  letI iR := ringMapAlgebra hFN
  letI : SMul (coordRing t F) (coordRing t N) := iR.toSMul
  letI := fieldInclusionAlgebra hFN
  have : FiniteDimensional (rationalBase k t) F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFN).toLinearMap
      (IntermediateField.inclusion hFN).injective
  have : IsScalarTower (coordRing t F) (coordRing t N) N := ⟨fun a b c => by
    change ((ringMap hFN a * b : coordRing t N) : N) * c =
      (IntermediateField.inclusion hFN (a : F)) * ((b : N) * c)
    rw [← mul_assoc]
    rfl⟩
  have : IsScalarTower (rationalBase k t) F N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsSeparable (rationalBase k t) F :=
    Algebra.IsSeparable.of_algHom (F := rationalBase k t) (E := F) (E' := N)
      (IntermediateField.inclusion hFN)
  have := fractionFieldRing t F
  have := fractionFieldRing t N
  have := dedekindRing t ht F
  have : Algebra.IsIntegral (coordRing t F) (coordRing t N) := ⟨ringMap_isIntegral hFN⟩
  have := fieldGaloisGroup_fixSub hFN
  exact IsGaloisGroup.of_isFractionRing (fixSub N F) (coordRing t F) (coordRing t N) F N

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
