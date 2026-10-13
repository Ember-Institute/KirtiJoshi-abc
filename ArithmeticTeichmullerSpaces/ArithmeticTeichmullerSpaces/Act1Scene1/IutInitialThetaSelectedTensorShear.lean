import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedTensorLogRegion
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarTransvection

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-SHEAR
source: actual selected tensor basis and normalized Haar measure;
the proved p-adic transvection Haar law.
fidelity: every elementary basis shear preserves actual selected tensor
region Haar volume. This is a determinant/Haar consumer, not a theta-hull
invariance claim or a paper-weighted volume computation.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.SelectedThetaTensor

open JoshiTeich.Prologue MeasureTheory
open scoped Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]

local instance indexFintype : Fintype (packet D p).BasisIndex := by infer_instance
local instance shearIntegralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

def shear (t : Matrix.TransvectionStruct (packet D p).BasisIndex ℚ_[p]) :
    (packet D p).Tensor ≃L[ℚ_[p]] (packet D p).Tensor :=
  PadicHaar.basisTransvection (packet D p).tensorBasis t

set_option maxHeartbeats 1000000 in
theorem shear_measurePreserving
    (t : Matrix.TransvectionStruct (packet D p).BasisIndex ℚ_[p]) :
    MeasurePreserving (shear D p t) (packet D p).normalizedHaar
      (packet D p).normalizedHaar := by
  letI : Module.Finite ℚ_[p] (packet D p).Tensor :=
    Module.Finite.of_basis (packet D p).tensorBasis
  exact PadicHaar.haar_measurePreserving_basisTransvection (packet D p).normalizedHaar
    (packet D p).tensorBasis t

theorem region_haar_shear_image
    (t : Matrix.TransvectionStruct (packet D p).BasisIndex ℚ_[p]) :
    (packet D p).normalizedHaar ((shear D p t) '' (region D p : Set (packet D p).Tensor)) =
      (packet D p).normalizedHaar (region D p) := by
  have hs : MeasurableSet ((shear D p t) '' (region D p : Set (packet D p).Tensor)) :=
    ((region_isCompact D p).image (shear D p t).continuous).measurableSet
  have h := (shear_measurePreserving D p t).measure_preimage hs.nullMeasurableSet
  rw [(shear D p t).injective.preimage_image] at h
  exact h.symm

theorem region_haar_shear_image_eq_inv_index
    (t : Matrix.TransvectionStruct (packet D p).BasisIndex ℚ_[p]) :
    (packet D p).normalizedHaar ((shear D p t) '' (region D p : Set (packet D p).Tensor)) =
      (regionIndex D p : ENNReal)⁻¹ := by
  rw [region_haar_shear_image, region_normalizedHaar_eq_inv_index]

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
