import Solutions.Source_ReferenceIutCor312CompletedGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltField

/-!
The automorphisms used by the local Kummer cocycle in Joshi III §9.6 act
coordinatewise on the pretilt of the same completed algebraic closure.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (p : ℕ)

local notation "𝒪" => LocalGeometricFontaine.integerRing (Field K)

/-- The valuation-ring automorphism induces an automorphism of its quotient by p. -/
def extendGaloisModP (σ : Algebraic K ≃ₐ[K] Algebraic K) :
    ModP 𝒪 p ≃+* ModP 𝒪 p :=
  Ideal.quotientEquiv _ _ (extendGaloisIntegers σ) (by
    rw [Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom, map_natCast])

theorem extendGaloisModP_mk (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : 𝒪) :
    extendGaloisModP p σ (Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) x) =
      Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (extendGaloisIntegers σ x) :=
  rfl

variable [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

/-- Acting on each coordinate preserves the compatibility under Frobenius. -/
def extendGaloisPreTilt (σ : Algebraic K ≃ₐ[K] Algebraic K) :
    GeometricTiltField.Source (Field K) p →+* GeometricTiltField.Source (Field K) p :=
  Perfection.map p (extendGaloisModP p σ).toRingHom

theorem coeff_extendGaloisPreTilt (σ : Algebraic K ≃ₐ[K] Algebraic K)
    (x : GeometricTiltField.Source (Field K) p) (n : ℕ) :
    Perfection.coeff (ModP 𝒪 p) p n (extendGaloisPreTilt p σ x) =
      extendGaloisModP p σ (Perfection.coeff (ModP 𝒪 p) p n x) :=
  rfl

end
end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
