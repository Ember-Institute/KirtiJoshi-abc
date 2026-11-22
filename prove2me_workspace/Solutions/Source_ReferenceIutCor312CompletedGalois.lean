import ArithmeticTeichmullerSpaces.Act1Scene1.CompletedAlgebraicClosure
import ArithmeticTeichmullerSpaces.Act1Scene1.AlgebraicallyClosedFontaine

/-!
For the Galois cohomology of the local field in Joshi III, §9.6, extend the
action on the algebraic roots to the same completed algebraic closure.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open UniformSpace

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

private theorem algebraic_isometry (σ : Algebraic K ≃ₐ[K] Algebraic K) :
    Isometry σ := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact (spectralNorm_eq_of_equiv σ (x - y)).symm

/-- An automorphism of the algebraic closure acts on its norm completion. -/
def extendGalois (σ : Algebraic K ≃ₐ[K] Algebraic K) : Field K ≃+* Field K :=
  Completion.mapRingEquiv σ.toRingEquiv
    (algebraic_isometry σ).continuous (algebraic_isometry σ.symm).continuous

theorem extendGalois_coe (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : Algebraic K) :
    extendGalois σ (x : Field K) = (σ x : Field K) :=
  Completion.mapRingHom_coe (algebraic_isometry σ).continuous x

theorem extendGalois_norm (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : Field K) :
    ‖extendGalois σ x‖ = ‖x‖ := by
  refine Completion.induction_on x (isClosed_eq ?_ continuous_norm) ?_
  · exact continuous_norm.comp Completion.continuous_map
  · intro a
    rw [extendGalois_coe, Completion.norm_coe, Completion.norm_coe]
    exact (spectralNorm_eq_of_equiv σ a).symm

/-- Extension of automorphisms preserves composition and the identity. -/
def galoisCompletion : (Algebraic K ≃ₐ[K] Algebraic K) →* (Field K ≃+* Field K) where
  toFun := extendGalois
  map_one' := by
    ext x : 1
    refine Completion.induction_on x (isClosed_eq Completion.continuous_map continuous_id) ?_
    intro a
    exact extendGalois_coe 1 a
  map_mul' σ τ := by
    ext x : 1
    refine Completion.induction_on x
      (isClosed_eq Completion.continuous_map
        (Completion.continuous_map.comp Completion.continuous_map)) ?_
    intro a
    change extendGalois (σ * τ) (a : Field K) =
      extendGalois σ (extendGalois τ (a : Field K))
    rw [extendGalois_coe, extendGalois_coe, extendGalois_coe]
    rfl

/-- The completed action restricts to the valuation integers used by Fontaine's map. -/
def extendGaloisIntegers (σ : Algebraic K ≃ₐ[K] Algebraic K) :
    LocalGeometricFontaine.integerRing (Field K) ≃+*
      LocalGeometricFontaine.integerRing (Field K) :=
  (extendGalois σ).restrict _ _ fun x => by
    rw [LocalGeometricFontaine.mem_integerRing, LocalGeometricFontaine.mem_integerRing,
      extendGalois_norm]

theorem extendGaloisIntegers_coe (σ : Algebraic K ≃ₐ[K] Algebraic K)
    (x : LocalGeometricFontaine.integerRing (Field K)) :
    (extendGaloisIntegers σ x : Field K) = extendGalois σ (x : Field K) := rfl

end
end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
