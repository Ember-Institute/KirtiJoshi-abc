import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedTensorLogRegion
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorDetHaar

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-DET-HAAR
source: actual selected logarithm scalars, tensor scaling matrix and algebraic
norm determinant formula, and the proved general p-adic Haar law.
fidelity: identifies the actual region Haar measure with its scaling
determinant norm and the product of factor algebraic norm moduli. Completion
norm/local-degree evaluation and paper volume correction remain separate.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.SelectedThetaTensor

open JoshiTeich.Prologue MeasureTheory
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]

local instance detIndexFintype : Fintype (packet D p).BasisIndex := by infer_instance
local instance detIntegralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])
local instance detTensorFinite : Module.Finite ℚ_[p] (packet D p).Tensor :=
  Module.Finite.of_basis (packet D p).tensorBasis
local instance detFactorAlgebra (i : Fin (Fintype.card ↥(fiber D p))) :
    Algebra ℚ_[p] ((packet D p).Factor i) :=
  LocalCompletion.padicAlgebra ((packet D p).residueChar_eq i)
local instance detFactorFinite (i : Fin (Fintype.card ↥(fiber D p))) :
    Module.Finite ℚ_[p] ((packet D p).Factor i) :=
  LocalCompletion.finite_padicAlgebra ((packet D p).residueChar_eq i)

private theorem logScalar_nonzero (i : Fin (Fintype.card ↥(fiber D p))) :
    iutInitialThetaFullQRootLogValue D (sourceAt D p i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero (sourceAt D p i))

def logScale : (packet D p).Tensor ≃L[ℚ_[p]] (packet D p).Tensor :=
  (packet D p).continuousScale (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D p i))
    (logScalar_nonzero D p)

def logScaleDet : ℚ_[p] :=
  (packet D p).scaleDet (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D p i))
    (logScalar_nonzero D p)

def logFactorNorm (i : Fin (Fintype.card ↥(fiber D p))) : ℚ_[p] :=
  @Algebra.norm ℚ_[p] ((packet D p).Factor i) _ _
    (LocalCompletion.padicAlgebra ((packet D p).residueChar_eq i))
    (iutInitialThetaFullQRootLogValue D (sourceAt D p i))

theorem region_eq_logScale_image :
    (region D p : Set (packet D p).Tensor) =
      (logScale D p) '' ((packet D p).unitLattice : Set (packet D p).Tensor) :=
  (LocalCompletion.Packet.unitLattice_image_scale (packet D p) _ (logScalar_nonzero D p)).symm

theorem region_normalizedHaar_eq_det_norm :
    (packet D p).normalizedHaar (region D p) = ENNReal.ofReal ‖logScaleDet D p‖ :=
  LocalCompletion.Packet.normalizedHaar_scalarLattice_eq_det_norm (packet D p)
    (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D p i)) (logScalar_nonzero D p)

theorem region_normalizedHaar_eq_factorNorm_product :
    (packet D p).normalizedHaar (region D p) =
      ENNReal.ofReal (∏ i, ‖logFactorNorm D p i‖ ^
        FiniteTensorMatrix.otherDimension
          (fun j => Module.finrank ℚ_[p] ((packet D p).Factor j)) i) :=
  LocalCompletion.Packet.normalizedHaar_scalarLattice_eq_factorNorm_product (packet D p)
    (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D p i)) (logScalar_nonzero D p)

theorem regionIndex_inv_eq_det_norm :
    (regionIndex D p : ENNReal)⁻¹ = ENNReal.ofReal ‖logScaleDet D p‖ := by
  rw [← region_normalizedHaar_eq_inv_index, region_normalizedHaar_eq_det_norm]

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
