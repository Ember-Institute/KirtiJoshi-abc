import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNormalizedOrbitProductThetaKernel
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNormalizedOrbitProductFiniteFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-NORMALIZED-ORBIT-PRODUCT-QUOTIENT-FROBENIUS
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, the primitive quotient of a theta-kernel period.
fidelity: combines the proved principal quotient of the nonzero normalized
orbit product with its Frobenius functional equation. The unique quotient
Q satisfying xi*Q=P is exactly scaleUnit*phi(P), by cancellation with xi.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this is a quotient recursion only. It does not
identify Q or P with a Tate period and does not prove the full phi=p kernel.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittNormalizedOrbitProductQuotientFrobenius

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittNormalizedOrbitProduct
open InitialThetaWittNormalizedOrbitProductThetaKernel
open InitialThetaWittNormalizedOrbitProductFiniteFrobenius
open InitialThetaWittThetaPrincipalKernel
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def primitiveProductQuotient : Carrier D w :=
  Classical.choose (existsUnique_primitive_product_quotient D w)

theorem primitive_mul_productQuotient :
    primitive D w * primitiveProductQuotient D w = product D w :=
  (Classical.choose_spec (existsUnique_primitive_product_quotient D w)).1

theorem productQuotient_eq_frobenius_scaled :
    primitiveProductQuotient D w =
      (scaleUnit D w : Carrier D w) *
        InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) := by
  apply (InitialThetaWittPrincipalIdealClosed.multiplication_isUniformEmbedding D w
    (primitive D w) (primitive_ne_zero D w)).injective
  calc
    primitive D w * primitiveProductQuotient D w = product D w :=
      primitive_mul_productQuotient D w
    _ = InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) *
        factor D w 0 :=
      (product_frobenius_mul_factor_zero D w).symm
    _ = primitive D w *
        ((scaleUnit D w : Carrier D w) *
          InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w)) := by
      rw [factor, InitialThetaWittFrobeniusThetaOrbit.primitiveOrbit_zero]
      ring

theorem productQuotient_eq_nextFactor_frobenius :
    primitiveProductQuotient D w = factor D w 1 *
      InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
        (primitiveProductQuotient D w) := by
  calc
    primitiveProductQuotient D w =
        (scaleUnit D w : Carrier D w) *
          InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) :=
      productQuotient_eq_frobenius_scaled D w
    _ = (scaleUnit D w : Carrier D w) *
        InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
          (primitive D w * primitiveProductQuotient D w) := by
      rw [primitive_mul_productQuotient]
    _ = factor D w 1 *
        InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
          (primitiveProductQuotient D w) := by
      rw [map_mul]
      change (scaleUnit D w : Carrier D w) *
          (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (primitive D w) *
            InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
              (primitiveProductQuotient D w)) = _
      have hφ : InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
          (primitive D w) = InitialThetaWittFrobeniusThetaOrbit.primitiveOrbit D w 1 := by
        rw [← InitialThetaWittFrobeniusThetaOrbit.primitiveOrbit_zero,
          ← InitialThetaWittFrobeniusThetaOrbit.primitiveOrbit_succ]
      rw [hφ, factor]
      rw [mul_assoc]

theorem primitiveProductQuotient_ne_zero : primitiveProductQuotient D w ≠ 0 := by
  intro hzero
  apply product_ne_zero D w
  rw [← primitive_mul_productQuotient, hzero, mul_zero]

theorem evaluate_primitiveProductQuotient_ne_zero (ρ : InitialThetaWittAllRadiusCompletion.Radius) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (primitiveProductQuotient D w) ≠ 0 := by
  intro h
  apply primitiveProductQuotient_ne_zero D w
  exact InitialThetaWittRadiusFaithfulness.evaluate_injective D w ρ
    (h.trans (map_zero _).symm)

theorem coordinateSeminorm_primitiveProductQuotient_pos
    (ρ : InitialThetaWittAllRadiusCompletion.Radius) :
    0 < InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (primitiveProductQuotient D w) := by
  exact norm_pos_iff.mpr (evaluate_primitiveProductQuotient_ne_zero D w ρ)

end
end JoshiTeich.Act1Scene1.InitialThetaWittNormalizedOrbitProductQuotientFrobenius
