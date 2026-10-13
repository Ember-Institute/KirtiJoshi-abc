import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedTensorArithmeticVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorDegreeVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-DEGREE-VOLUME
source: actual selected tensor region, raw Haar and arithmetic local degrees.
fidelity: computes the dimension-normalized Haar volume and its negative
logarithm using actual roots. Its weights are 1/(e*f); this does not identify
them with Joshi III eq:weights, inverse relative degrees, or the earlier
paper uniformizer correction 1/f. No theta hull is constructed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.SelectedThetaTensor
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]
local instance degreeIntegralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

private theorem logValue_nonzero (i : Fin (Fintype.card ↥(fiber D p))) :
    iutInitialThetaFullQRootLogValue D (sourceAt D p i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero (sourceAt D p i))

private theorem logValue_contracting (i : Fin (Fintype.card ↥(fiber D p))) :
    ‖iutInitialThetaFullQRootLogValue D (sourceAt D p i)‖ < 1 := by
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact iutInitialThetaFullQRoot_norm_lt_one D _

theorem region_degreeLogVolume_eq_rootNorm_sum :
    (packet D p).degreeLogVolume (region D p) =
      ∑ i, Real.log ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)‖ /
        (Arithmetic.localDeg (sourceAt D p i).1 : ℝ) := by
  have h := (packet D p).degreeLogVolume_scalarLattice_eq_norm_sum
    (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D p i))
    (logValue_nonzero D p) (logValue_contracting D p)
  change (packet D p).degreeLogVolume (region D p) =
    ∑ i, Real.log ‖iutInitialThetaFullQRootLogValue D (sourceAt D p i)‖ /
      (Arithmetic.localDeg (sourceAt D p i).1 : ℝ) at h
  simpa only [iutInitialThetaFullQRootLogValue_norm_eq] using h

theorem region_degreeVolume_eq_rootNorm_product :
    (packet D p).degreeVolume (region D p) =
      ∏ i, ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)‖ ^
        (1 / (Arithmetic.localDeg (sourceAt D p i).1 : ℝ)) := by
  have h := (packet D p).degreeVolume_scalarLattice_eq_norm_product
    (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D p i))
    (logValue_nonzero D p) (logValue_contracting D p)
  change (packet D p).degreeVolume (region D p) =
    ∏ i, ‖iutInitialThetaFullQRootLogValue D (sourceAt D p i)‖ ^
      (1 / (Arithmetic.localDeg (sourceAt D p i).1 : ℝ)) at h
  simpa only [iutInitialThetaFullQRootLogValue_norm_eq] using h

theorem region_degreeVolume_negLog_eq_ordp_sum :
    -Real.log ((packet D p).degreeVolume (region D p)) =
      ∑ i, Arithmetic.ordp (sourceAt D p i).1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)) *
          Real.log p := by
  rw [region_degreeVolume_eq_rootNorm_product,
    Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (norm_pos_iff.mpr
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)) _).ne'),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_rpow (norm_pos_iff.mpr
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _))]
  unfold Arithmetic.ordp
  rw [(sourceAt_selected_residueChar D p i).2]
  have hd : (Arithmetic.localDeg (sourceAt D p i).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.localDeg_pos _).ne'
  have hp : Real.log p ≠ 0 := (Real.log_pos
    (by exact_mod_cast (Fact.out : p.Prime).one_lt)).ne'
  field_simp [hd, hp]
  <;> ring

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
