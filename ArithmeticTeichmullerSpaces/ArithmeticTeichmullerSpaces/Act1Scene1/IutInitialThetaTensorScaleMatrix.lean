import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTensorIntegralBasis
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScaleMatrix

/-!
source-id: JT-SCENE1-INITIAL-THETA-TENSOR-SCALE-MATRIX
fidelity: constructs the actual canonical logarithm scaling matrix,
proves its determinant nonzero and identifies it in the actual region's
rational basis and as a product of actual factor algebraic norms.
Absolute-norm normalization, Haar/index evaluation and paper weighted
volume remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTensorWitness

open JoshiTeich.Prologue NumberField
open scoped BigOperators

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι]
variable (c : ι → (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset)
variable (hc : ∀ i, Arithmetic.residueChar (c i).1 = p)

local instance matrixIndexFintype : Fintype (packet D p c hc).BasisIndex :=
  by classical infer_instance
local instance commonFactorAlgebra (i : ι) :
    Algebra ℚ_[p] ((packet D p c hc).Factor i) :=
  LocalCompletion.padicAlgebra ((packet D p c hc).residueChar_eq i)
local instance commonFactorFinite (i : ι) :
    Module.Finite ℚ_[p] ((packet D p c hc).Factor i) :=
  LocalCompletion.finite_padicAlgebra ((packet D p c hc).residueChar_eq i)

def scaleMatrix : Matrix (packet D p c hc).BasisIndex (packet D p c hc).BasisIndex ℚ_[p] :=
  (packet D p c hc).scaleMatrix (fun i => InitialThetaLogWitness.value D (c i))
    (fun i => InitialThetaLogWitness.value_ne_zero D (c i))

theorem scaleMatrix_det_eq :
    (scaleMatrix D p c hc).det = LinearMap.det (scale D p c hc).toLinearEquiv.toLinearMap :=
  LocalCompletion.Packet.scaleMatrix_det_eq (packet D p c hc) _ _

theorem scaleMatrix_det_ne_zero : (scaleMatrix D p c hc).det ≠ 0 :=
  LocalCompletion.Packet.scaleMatrix_det_ne_zero (packet D p c hc) _ _

/-- The factor matrix and the actual region basis give the same scaling determinant. -/
theorem scaleMatrix_det_eq_regionBasis :
    (scaleMatrix D p c hc).det =
      (LinearMap.toMatrix (regionRationalBasis D p c hc) (regionRationalBasis D p c hc)
        (scale D p c hc).toLinearEquiv.toLinearMap).det := by
  rw [LinearMap.det_toMatrix]
  exact scaleMatrix_det_eq D p c hc

/-- The local multiplication matrix uses the actual canonical logarithm scalar. -/
def factorLogMulMatrix (i : ι) :=
  (packet D p c hc).factorMulMatrix i (InitialThetaLogWitness.value D (c i))

/-- The actual algebraic norm down to `ℚ_p`, with the source completion's algebra structure. -/
def factorLogNorm (i : ι) : ℚ_[p] :=
  @Algebra.norm ℚ_[p] ((packet D p c hc).Factor i) _ _
    (LocalCompletion.padicAlgebra ((packet D p c hc).residueChar_eq i))
    (InitialThetaLogWitness.value D (c i))

theorem factorLogMulMatrix_det_eq_norm (i : ι) :
    (factorLogMulMatrix D p c hc i).det = factorLogNorm D p c hc i :=
  LocalCompletion.Packet.factorMulMatrix_det_eq_norm (packet D p c hc) i _

theorem factorLogMulMatrix_det_ne_zero (i : ι) :
    (factorLogMulMatrix D p c hc i).det ≠ 0 :=
  LocalCompletion.Packet.factorMulMatrix_det_ne_zero (packet D p c hc) i _
    (InitialThetaLogWitness.value_ne_zero D (c i))

theorem scaleMatrix_eq_factorLogMul_prod (k l : (packet D p c hc).BasisIndex) :
    scaleMatrix D p c hc k l = ∏ i, factorLogMulMatrix D p c hc i (k i) (l i) :=
  LocalCompletion.Packet.scaleMatrix_eq_factorMul_prod (packet D p c hc) _ _ k l

theorem scaleMatrix_det_eq_factorLogNorm_prod :
    (scaleMatrix D p c hc).det =
      ∏ i, factorLogNorm D p c hc i ^
        FiniteTensorMatrix.otherDimension
          (fun j => @Module.finrank ℚ_[p] ((packet D p c hc).Factor j) _ _
            (LocalCompletion.padicAlgebra ((packet D p c hc).residueChar_eq j)).toModule) i :=
  LocalCompletion.Packet.scaleMatrix_det_eq_factor_norm_prod (packet D p c hc) _ _

def commonPadicScaleMatrix (a : ℚ_[p]) (ha : a ≠ 0) :
    Matrix (packet D p c hc).BasisIndex (packet D p c hc).BasisIndex ℚ_[p] :=
  (packet D p c hc).scaleMatrix
    (fun i => algebraMap ℚ_[p] ((packet D p c hc).Factor i) a)
    (fun i => by
      intro h
      exact ha ((algebraMap ℚ_[p] ((packet D p c hc).Factor i)).injective (by simpa using h)))

theorem commonPadicScaleMatrix_det_eq_pow (a : ℚ_[p]) (ha : a ≠ 0) :
    (commonPadicScaleMatrix D p c hc a ha).det =
      a ^ (Fintype.card ι * ∏ i, Module.finrank ℚ_[p] ((packet D p c hc).Factor i)) :=
  LocalCompletion.Packet.scaleMatrix_det_common_algebraMap (packet D p c hc) a ha

theorem commonPadicScaleMatrix_det_eq_prime_pow :
    (commonPadicScaleMatrix D p c hc (p : ℚ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).det =
      (p : ℚ_[p]) ^ (Fintype.card ι * ∏ i, Module.finrank ℚ_[p] ((packet D p c hc).Factor i)) :=
  commonPadicScaleMatrix_det_eq_pow D p c hc _ _

end
end JoshiTeich.Act1Scene1.InitialThetaTensorWitness
