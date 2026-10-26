import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenKernelTwistedComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-KERNEL-FIRST-ORDER
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`,
the theta kernel in the full Frobenius period space.
fidelity: actual division by the nonzero orbit product gives a
continuous Q_p-linear evaluation on the entire eigen theta kernel.
Its kernel consists exactly of elements divisible by xi^2 in the
original common ring. This uses theta(P/xi) nonzero and the proved
principal theta kernel, not a first-order comparison assumption.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no injectivity, image classification or
Tate-period identification is asserted. The original full kernel,
topology and Prologue R5 are retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelFirstOrder

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittNormalizedOrbitProduct InitialThetaWittThetaPrincipalKernel
open InitialThetaWittNormalizedOrbitProductQuotientFrobenius
open InitialThetaWittOrbitProductSimpleThetaZero
open InitialThetaWittEigenKernelTwistedComparison
open InitialThetaWittThetaEvaluation InitialThetaWittThetaBound
open InitialThetaWittThetaPadicCompatibility
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem primitive_sq_dvd_product_mul_iff (y : Carrier D w) :
    primitive D w ^ 2 ∣ product D w * y ↔ evaluation D w y = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    have he : primitiveProductQuotient D w * y = primitive D w * a := by
      apply (InitialThetaWittPrincipalIdealClosed.multiplication_isUniformEmbedding D w
        (primitive D w) (primitive_ne_zero D w)).injective
      change primitive D w * (primitiveProductQuotient D w * y) = primitive D w * (primitive D w * a)
      calc
        _ = product D w * y := by rw [← mul_assoc, primitive_mul_productQuotient]
        _ = primitive D w ^ 2 * a := ha
        _ = _ := by ring
    have hz : evaluation D w (primitiveProductQuotient D w * y) = 0 := by
      rw [he, map_mul, evaluation_primitive, zero_mul]
    rw [map_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (evaluation_productQuotient_ne_zero D w)
  · intro hy
    obtain ⟨a, ha⟩ := (evaluation_eq_zero_iff_dvd D w y).mp hy
    refine ⟨primitiveProductQuotient D w * a, ?_⟩
    rw [← primitive_mul_productQuotient, ha, pow_two]
    ring

def quotientEvaluation : fullKernel D w →L[Padic (Arithmetic.residueChar w.1)] Untilt D w :=
  (evaluationContinuousLinear D w).comp
    ((twistedSubmodule D w).subtypeL.comp (productContinuousLinearEquiv D w).symm.toContinuousLinearMap)

theorem quotientEvaluation_apply (x : fullKernel D w) :
    quotientEvaluation D w x =
      evaluation D w (((productContinuousLinearEquiv D w).symm x).val) := rfl

theorem quotientEvaluation_multiplyProduct (y : twistedSubmodule D w) :
    quotientEvaluation D w (multiplyProduct D w y) = evaluation D w y.val := by
  change evaluation D w
      (((productContinuousLinearEquiv D w).symm (productContinuousLinearEquiv D w y)).val) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem primitive_sq_dvd_iff_quotientEvaluation_zero (x : fullKernel D w) :
    primitive D w ^ 2 ∣ x.val ↔ quotientEvaluation D w x = 0 := by
  have hx : product D w * (((productContinuousLinearEquiv D w).symm x).val) = x.val :=
    congrArg Subtype.val ((productContinuousLinearEquiv D w).apply_symm_apply x)
  change primitive D w ^ 2 ∣ x.val ↔
    evaluation D w (((productContinuousLinearEquiv D w).symm x).val) = 0
  rw [← hx, primitive_sq_dvd_product_mul_iff]

theorem mem_quotientEvaluation_kernel (x : fullKernel D w) :
    x ∈ (quotientEvaluation D w).ker ↔ primitive D w ^ 2 ∣ x.val :=
  (primitive_sq_dvd_iff_quotientEvaluation_zero D w x).symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelFirstOrder
