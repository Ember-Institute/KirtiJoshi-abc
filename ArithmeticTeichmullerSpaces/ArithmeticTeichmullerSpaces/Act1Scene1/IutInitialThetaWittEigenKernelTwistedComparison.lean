import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenKernelInfiniteDivision
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittOrbitProductSimpleThetaZero
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenRadiusTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaPadicQuotient
import Mathlib.Topology.Algebra.Module.Equiv

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-KERNEL-TWISTED-COMPARISON
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`,
the full B^{phi=p} evaluation kernel and primitive Frobenius factors.
fidelity: multiplication by the actual nonzero orbit product P gives
a continuous Q_p-linear equivalence from the actual closed subspace
phi(y)=p*f_0*y onto the entire phi=p theta kernel. Surjectivity is
proved by the existing infinite-product division theorem. The equation
follows by cancellation in phi(P)*f_0=P. The inverse is continuous for
the original topology by the proved inducing multiplication map.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no twisted-solution existence or dimension
law is input. Neither space is replaced by a principal-log image.
Full Tate-kernel identity and twisted-solution classification remain open.
Original carrier, scalar action and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelTwistedComparison

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittAdditiveTatePeriod
open InitialThetaWittNormalizedOrbitProduct InitialThetaWittNormalizedOrbitProductFiniteFrobenius
open InitialThetaWittThetaEvaluation InitialThetaWittThetaPadicCompatibility
open InitialThetaWittPrincipalIdealClosed
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def multiplicationContinuousLinear (a : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    InitialThetaWittAllRadiusCompletion.Carrier D w →L[Padic (Arithmetic.residueChar w.1)]
      InitialThetaWittAllRadiusCompletion.Carrier D w where
  toFun y := a * y
  map_add' x y := mul_add a x y
  map_smul' c y := mul_smul_comm c a y
  cont := continuous_const.mul continuous_id

def frobeniusContinuousLinear :
    InitialThetaWittAllRadiusCompletion.Carrier D w →L[Padic (Arithmetic.residueChar w.1)]
      InitialThetaWittAllRadiusCompletion.Carrier D w where
  __ := (frobeniusAlgEquiv D w).toLinearMap
  cont := frobeniusAlgEquiv_continuous D w

def twistedSubmodule : Submodule (Padic (Arithmetic.residueChar w.1))
    (InitialThetaWittAllRadiusCompletion.Carrier D w) :=
  (frobeniusContinuousLinear D w - multiplicationContinuousLinear D w
    ((Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) * factor D w 0)).ker

theorem mem_twistedSubmodule (y : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    y ∈ twistedSubmodule D w ↔
      InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w y =
        (Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) *
          factor D w 0 * y := by
  change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w y -
    ((Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) *
      factor D w 0) * y = 0 ↔ _
  exact sub_eq_zero

theorem twistedSubmodule_isClosed : IsClosed
    (twistedSubmodule D w : Set (InitialThetaWittAllRadiusCompletion.Carrier D w)) :=
  (frobeniusContinuousLinear D w - multiplicationContinuousLinear D w
    ((Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) * factor D w 0)).isClosed_ker

def fullKernel : Submodule (Padic (Arithmetic.residueChar w.1))
    (InitialThetaWittAllRadiusCompletion.Carrier D w) :=
  frobeniusPrimeSubmodule D w ⊓ InitialThetaWittThetaPadicQuotient.kernelSubmodule D w

theorem mem_fullKernel (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    x ∈ fullKernel D w ↔
      InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x =
        (Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) * x ∧
      evaluation D w x = 0 := by
  change (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x =
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x ∧
      evaluation D w x = 0) ↔ _
  simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem fullKernel_isClosed : IsClosed
    (fullKernel D w : Set (InitialThetaWittAllRadiusCompletion.Carrier D w)) := by
  change IsClosed ((frobeniusPrimeSubmodule D w :
    Set (InitialThetaWittAllRadiusCompletion.Carrier D w)) ∩
    (InitialThetaWittThetaPadicQuotient.kernelSubmodule D w :
      Set (InitialThetaWittAllRadiusCompletion.Carrier D w)))
  exact (InitialThetaWittEigenRadiusTopology.eigen_isClosed D w).inter
    (InitialThetaWittThetaPadicQuotient.kernelSubmodule_isClosed D w)

theorem frobenius_product_ne_zero :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) ≠ 0 := by
  intro h
  exact product_ne_zero D w
    ((InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).injective
      (h.trans (map_zero _).symm))

theorem mem_fullKernel_product_iff (y : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    product D w * y ∈ fullKernel D w ↔ y ∈ twistedSubmodule D w := by
  rw [mem_fullKernel, mem_twistedSubmodule]
  constructor
  · rintro ⟨he, _⟩
    apply (multiplication_isUniformEmbedding D w
      (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w))
      (frobenius_product_ne_zero D w)).injective
    change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) *
        InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w y =
      InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) *
        ((Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) *
          factor D w 0 * y)
    calc
      InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) *
          InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w y =
        (Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) *
          (product D w * y) := by rw [← map_mul]; exact he
      _ = (Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) *
          ((InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) *
            factor D w 0) * y) :=
        congrArg (fun z : InitialThetaWittAllRadiusCompletion.Carrier D w =>
          (Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) *
            (z * y)) (product_frobenius_mul_factor_zero D w).symm
      _ = _ := by ring
  · intro he
    constructor
    · rw [map_mul, he]
      calc
        _ = (Arithmetic.residueChar w.1 : InitialThetaWittAllRadiusCompletion.Carrier D w) *
          (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) * factor D w 0) * y := by ring
        _ = _ := by rw [product_frobenius_mul_factor_zero]; ring
    · rw [map_mul, InitialThetaWittNormalizedOrbitProductThetaKernel.evaluation_product_eq_zero, zero_mul]

def multiplyProduct : twistedSubmodule D w →L[Padic (Arithmetic.residueChar w.1)] fullKernel D w where
  toFun y := ⟨product D w * y.val, (mem_fullKernel_product_iff D w y.val).mpr y.property⟩
  map_add' x y := Subtype.ext (mul_add (product D w) x.val y.val)
  map_smul' c y := Subtype.ext (mul_smul_comm c (product D w) y.val)
  cont := (continuous_const.mul continuous_subtype_val).subtype_mk _

theorem multiplyProduct_apply (y : twistedSubmodule D w) :
    (multiplyProduct D w y).val = product D w * y.val := rfl

theorem multiplyProduct_injective : Function.Injective (multiplyProduct D w) := by
  intro x y h
  apply Subtype.ext
  apply (multiplication_isUniformEmbedding D w (product D w) (product_ne_zero D w)).injective
  exact congrArg Subtype.val h

theorem multiplyProduct_surjective : Function.Surjective (multiplyProduct D w) := by
  intro x
  have hx : x.val ∈ frobeniusPrimeSubmodule D w ∧ evaluation D w x.val = 0 := x.property
  obtain ⟨y, hy, _⟩ := InitialThetaWittEigenKernelInfiniteDivision.existsUnique_product_quotient
    D w ⟨x.val, hx.1⟩ hx.2
  have hyK : product D w * y ∈ fullKernel D w := by rw [hy]; exact x.property
  refine ⟨⟨y, (mem_fullKernel_product_iff D w y).mp hyK⟩, ?_⟩
  exact Subtype.ext hy

def productLinearEquiv : twistedSubmodule D w ≃ₗ[Padic (Arithmetic.residueChar w.1)] fullKernel D w :=
  LinearEquiv.ofBijective (multiplyProduct D w).toLinearMap
    ⟨multiplyProduct_injective D w, multiplyProduct_surjective D w⟩

theorem productLinearEquiv_apply (y : twistedSubmodule D w) :
    (productLinearEquiv D w y).val = product D w * y.val := rfl

theorem productLinearEquiv_symm_continuous : Continuous (productLinearEquiv D w).symm := by
  have hval : Continuous (fun x : fullKernel D w => ((productLinearEquiv D w).symm x).val) := by
    apply (multiplication_isInducing D w (product D w) (product_ne_zero D w)).continuous_iff.mpr
    have heq : (fun x : fullKernel D w => multiplication D w (product D w)
        (((productLinearEquiv D w).symm x).val)) = (fun x => x.val) := by
      funext x
      exact congrArg Subtype.val ((productLinearEquiv D w).apply_symm_apply x)
    simpa only [Function.comp_def, heq] using
      (continuous_subtype_val : Continuous (fun x : fullKernel D w => x.val))
  exact hval.subtype_mk _

def productContinuousLinearEquiv :
    twistedSubmodule D w ≃L[Padic (Arithmetic.residueChar w.1)] fullKernel D w where
  __ := productLinearEquiv D w
  continuous_toFun := (multiplyProduct D w).continuous
  continuous_invFun := productLinearEquiv_symm_continuous D w

theorem productContinuousLinearEquiv_apply (y : twistedSubmodule D w) :
    (productContinuousLinearEquiv D w y).val = product D w * y.val := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelTwistedComparison
