/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/U2/GaloisClosure.lean and OrbicurveCores/U2/CoreMap.lean
-/
import Solutions.Source_ReferenceIutCanLiftGaloisCore
import Solutions.Source_ReferenceIutCanLiftNormalizationEmbed
import Mathlib.RingTheory.IsGaloisGroup.Defs

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
variable {F L N : IntermediateField (rationalBase k t) Ω}

local notation "M" => (galoisClosure (N := N) F L)

/-- The coordinate ring of the relative closure embeds in the ambient Galois extension. -/
private noncomputable def closureRingToField : coordRing t M →ₐ[k] N where
  toFun b := ⟨((b : M) : Ω), galoisClosure_le (b : M).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem closureRingToField_injective :
    Function.Injective (closureRingToField (N := N) (F := F) (L := L)) :=
  fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x : N => (x : Ω)) h))

private theorem isIntegral_apply_closureRingToField (σ : N ≃ₐ[rationalBase k t] N)
    (b : coordRing t M) :
    IsIntegral (polynomialBase k t)
      ((σ (closureRingToField (N := N) b) : N) : Ω) := by
  letI : IsScalarTower (polynomialBase k t) N Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hb : IsIntegral (polynomialBase k t) (closureRingToField (N := N) b) :=
    (isIntegral_algebraMap_iff (A := N) (B := Ω) (algebraMap N Ω).injective).mp
      (isIntegral_of_mem_coordRing t b)
  have hσb := hb.map ((σ : N →ₐ[rationalBase k t] N).restrictScalars (polynomialBase k t))
  exact (isIntegral_algebraMap_iff (A := N) (B := Ω) (algebraMap N Ω).injective).mpr hσb

private noncomputable def restrictClosureAlgHom (σ : N ≃ₐ[rationalBase k t] N)
    (hσ : σ ∈ fixSub N F) : coordRing t M →ₐ[k] coordRing t M where
  toFun b := by
    have hb : ((b : M) : Ω) ∈ M := (b : M).2
    have hσb := apply_mem_galoisClosure (y := closureRingToField (N := N) b) hσ hb
    exact ⟨⟨_, hσb⟩,
      mem_coordRing_of_isIntegral t hσb (isIntegral_apply_closureRingToField σ b)⟩
  map_one' := closureRingToField_injective (by
    change σ (closureRingToField (N := N) (1 : coordRing t M)) = _
    simp only [map_one])
  map_mul' a b := closureRingToField_injective (by
    change σ (closureRingToField (N := N) (a * b)) =
      σ (closureRingToField (N := N) a) * σ (closureRingToField (N := N) b)
    rw [map_mul, map_mul])
  map_zero' := closureRingToField_injective (by
    change σ (closureRingToField (N := N) (0 : coordRing t M)) = _
    simp only [map_zero])
  map_add' a b := closureRingToField_injective (by
    change σ (closureRingToField (N := N) (a + b)) =
      σ (closureRingToField (N := N) a) + σ (closureRingToField (N := N) b)
    rw [map_add, map_add])
  commutes' c := closureRingToField_injective (by
    change σ (closureRingToField (N := N) (algebraMap k (coordRing t M) c)) =
      closureRingToField (N := N) (algebraMap k (coordRing t M) c)
    rw [AlgHom.commutes]
    exact σ.commutes (algebraMap k (rationalBase k t) c))

private theorem closureRingToField_restrictClosureAlgHom (σ : N ≃ₐ[rationalBase k t] N)
    (hσ : σ ∈ fixSub N F) (b : coordRing t M) :
    closureRingToField (N := N) (restrictClosureAlgHom σ hσ b) =
      σ (closureRingToField (N := N) b) := rfl

private noncomputable def restrictClosureAlgEquiv (σ : N ≃ₐ[rationalBase k t] N)
    (hσ : σ ∈ fixSub N F) : coordRing t M ≃ₐ[k] coordRing t M :=
  AlgEquiv.ofAlgHom (restrictClosureAlgHom σ hσ)
    (restrictClosureAlgHom σ⁻¹ ((fixSub N F).inv_mem hσ))
    (AlgHom.ext fun b => closureRingToField_injective (by
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id,
        closureRingToField_restrictClosureAlgHom]
      exact σ.apply_symm_apply _))
    (AlgHom.ext fun b => closureRingToField_injective (by
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id,
        closureRingToField_restrictClosureAlgHom]
      exact σ.symm_apply_apply _))

/-- Restriction of the Galois group over the target to the closure coordinate ring. -/
private noncomputable def closureRestriction :
    fixSub N F →* (coordRing t M ≃ₐ[k] coordRing t M) where
  toFun σ := restrictClosureAlgEquiv σ σ.2
  map_one' := by
    apply AlgEquiv.ext
    intro b
    apply closureRingToField_injective
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro b
    apply closureRingToField_injective
    rfl

/-- The faithful action uses the image of the restriction to the closure coordinate ring. -/
noncomputable def galoisClosureAutomorphisms :
    Subgroup (coordRing t M ≃ₐ[k] coordRing t M) :=
  (closureRestriction (N := N) (F := F) (L := L)).range

theorem galoisClosure_isGaloisGroup [FiniteDimensional (rationalBase k t) N]
    [IsGalois (rationalBase k t) N] (hFM : F ≤ M) :
    letI := ringMapAlgebra hFM
    IsGaloisGroup (galoisClosureAutomorphisms (N := N) (F := F) (L := L))
      (coordRing t F) (coordRing t M) := by
  letI iR := ringMapAlgebra hFM
  letI : SMul (coordRing t F) (coordRing t M) := iR.toSMul
  let G := galoisClosureAutomorphisms (N := N) (F := F) (L := L)
  change IsGaloisGroup G (coordRing t F) (coordRing t M)
  refine { faithful := inferInstance, commutes := ⟨?_⟩, isInvariant := ⟨?_⟩ }
  · intro g a b
    have hfixed : g.val (ringMap hFM a) = ringMap hFM a := by
      obtain ⟨σ, hσ⟩ := g.2
      apply closureRingToField_injective
      rw [← hσ]
      exact (mem_fixSub.mp σ.2) _ (a : F).2
    change g.val (ringMap hFM a * b) = ringMap hFM a * g.val b
    rw [map_mul, hfixed]
  · intro b hb
    have hFN : F ≤ N := hFM.trans galoisClosure_le
    have hfixed : ((b : M) : Ω) ∈ F := mem_of_forall_fixSub hFN
      (y := closureRingToField (N := N) b) (fun σ hσ => by
        let τ : fixSub N F := ⟨σ, hσ⟩
        let g : G := ⟨closureRestriction (L := L) τ, ⟨τ, rfl⟩⟩
        exact congrArg (closureRingToField (N := N)) (hb g))
    refine ⟨⟨⟨_, hfixed⟩, mem_coordRing_of_isIntegral t hfixed (isIntegral_of_mem_coordRing t b)⟩, ?_⟩
    exact Subtype.ext (Subtype.ext rfl)

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
