import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittUntiltScalarNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenBanach

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-UNTILT-BANACH-VIEW
source: Joshi II `se:ff-rings` and the canonical untilt target of the
period sequence in the proof of `pr:teichmuller-lift-A`.
fidelity: gives a norm view of the original untilt, with norm equal to
the proved positive calibration power of its original field norm.
Proves equality of uniformities before installing the normed group.
The original Q_p action is standard-norm homogeneous and complete.
An explicit continuous linear equivalence returns to the original untilt;
its field norm and field structure are not replaced.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no new field or completion is selected.
The period kernel comparison remains open. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittUntiltBanachView

open JoshiTeich.Prologue InitialThetaWittThetaBound
open InitialThetaWittScalarCalibration InitialThetaWittUntiltScalarNorm
open scoped Topology Uniformity
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def NormView := Untilt D w

instance viewAddCommGroup : AddCommGroup (NormView D w) := inferInstanceAs (AddCommGroup (Untilt D w))
instance viewModule : Module (Padic (Arithmetic.residueChar w.1)) (NormView D w) :=
  inferInstanceAs (Module (Padic (Arithmetic.residueChar w.1)) (Untilt D w))
instance viewUniformSpace : UniformSpace (NormView D w) := inferInstanceAs (UniformSpace (Untilt D w))
instance viewUniformAddGroup : IsUniformAddGroup (NormView D w) :=
  inferInstanceAs (IsUniformAddGroup (Untilt D w))
instance viewComplete : CompleteSpace (NormView D w) := inferInstanceAs (CompleteSpace (Untilt D w))

def originalEquiv : NormView D w ≃ₗ[Padic (Arithmetic.residueChar w.1)] Untilt D w :=
  LinearEquiv.refl _ _

def value (x : NormView D w) : ℝ := ‖originalEquiv D w x‖ ^ exponent D w (radius D w)

theorem value_nonneg (x : NormView D w) : 0 ≤ value D w x := Real.rpow_nonneg (norm_nonneg _) _

theorem value_add_le_max (x y : NormView D w) :
    value D w (x + y) ≤ max (value D w x) (value D w y) := by
  unfold value
  rw [map_add]
  exact (Real.rpow_le_rpow (norm_nonneg _)
    (IsUltrametricDist.norm_add_le_max _ _) (exponent_pos D w (radius D w)).le).trans_eq
      (PositivePowerCalibration.rpow_max _ _ _ (norm_nonneg _) (norm_nonneg _)
        (exponent_pos D w (radius D w)).le)

def calibratedSeminorm : Seminorm (Padic (Arithmetic.residueChar w.1)) (NormView D w) :=
  Seminorm.of (value D w)
    (fun x y => (value_add_le_max D w x y).trans
      (max_le (le_add_of_nonneg_right (value_nonneg D w y))
        (le_add_of_nonneg_left (value_nonneg D w x))))
    (fun a x => by
      change ‖originalEquiv D w (a • x)‖ ^ exponent D w (radius D w) = _
      rw [map_smul]
      exact norm_smul_calibrated D w a (originalEquiv D w x))

theorem calibratedSeminorm_eq_zero_iff (x : NormView D w) :
    calibratedSeminorm D w x = 0 ↔ x = 0 := by
  constructor
  · intro h
    change ‖originalEquiv D w x‖ ^ exponent D w (radius D w) = 0 at h
    have hn : ‖originalEquiv D w x‖ = 0 := by
      rw [← Real.rpow_rpow_inv (norm_nonneg _) (exponent_pos D w (radius D w)).ne', h,
        Real.zero_rpow (inv_pos.mpr (exponent_pos D w (radius D w))).ne']
    apply (originalEquiv D w).injective
    simpa only [map_zero] using norm_eq_zero.mp hn
  · rintro rfl
    exact map_zero _

theorem tendsto_zero_iff_calibratedSeminorm {ι : Type*} (l : Filter ι) (f : ι → NormView D w) :
    Filter.Tendsto f l (𝓝 0) ↔ Filter.Tendsto (fun i => calibratedSeminorm D w (f i)) l (𝓝 0) := by
  change Filter.Tendsto (fun i => originalEquiv D w (f i)) l (𝓝 (0 : Untilt D w)) ↔ _
  have hraw : Filter.Tendsto (fun i => originalEquiv D w (f i)) l (𝓝 (0 : Untilt D w)) ↔
      Filter.Tendsto (fun i => ‖originalEquiv D w (f i)‖) l (𝓝 (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero
  exact hraw.trans (PositivePowerCalibration.tendsto_rpow_zero_iff l
    (fun i => ‖originalEquiv D w (f i)‖) (fun i => norm_nonneg _)
    (exponent D w (radius D w)) (exponent_pos D w (radius D w))).symm

theorem withCalibratedSeminorm : WithSeminorms (fun _ : Unit => calibratedSeminorm D w) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, iInf_const]
  apply le_antisymm
  · exact ((tendsto_zero_iff_calibratedSeminorm D w (𝓝 (0 : NormView D w)) id).mp
      Filter.tendsto_id).le_comap
  · have h := (tendsto_zero_iff_calibratedSeminorm D w
      (Filter.comap (calibratedSeminorm D w) (𝓝 (0 : ℝ))) id).mpr Filter.tendsto_comap
    exact Filter.tendsto_id'.mp h

theorem uniformSpace_eq_calibrated : (inferInstance : UniformSpace (NormView D w)) =
    (calibratedSeminorm D w).toSeminormedAddCommGroup.toUniformSpace := by
  have h := (SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf
    (fun _ : Unit => calibratedSeminorm D w)).mp (withCalibratedSeminorm D w)
  simpa only [iInf_const] using h

def calibratedNorm : AddGroupNorm (NormView D w) where
  __ := (calibratedSeminorm D w).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' x := (calibratedSeminorm_eq_zero_iff D w x).mp

theorem uniformity_eq_calibrated : 𝓤 (NormView D w) =
    𝓤[(calibratedNorm D w).toNormedAddCommGroup.toUniformSpace] :=
  congrArg (fun U : UniformSpace (NormView D w) => 𝓤[U]) (uniformSpace_eq_calibrated D w)

instance viewNormedAddCommGroup : NormedAddCommGroup (NormView D w) :=
  { (calibratedNorm D w).toNormedAddCommGroup with
    toMetricSpace := (calibratedNorm D w).toNormedAddCommGroup.toMetricSpace.replaceUniformity
      (uniformity_eq_calibrated D w) }

instance viewNormedSpace : NormedSpace (Padic (Arithmetic.residueChar w.1)) (NormView D w) where
  toModule := inferInstance
  norm_smul_le a x := (map_smul_eq_mul (calibratedSeminorm D w) a x).le

theorem norm_eq_original_power (x : NormView D w) :
    ‖x‖ = ‖originalEquiv D w x‖ ^ exponent D w (radius D w) := rfl

def originalContinuousLinearEquiv : NormView D w ≃L[Padic (Arithmetic.residueChar w.1)] Untilt D w where
  toLinearEquiv := originalEquiv D w
  continuous_toFun := uniformContinuous_id.continuous
  continuous_invFun := uniformContinuous_id.continuous

theorem norm_originalInverse (y : Untilt D w) :
    ‖(originalContinuousLinearEquiv D w).symm y‖ = ‖y‖ ^ exponent D w (radius D w) := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittUntiltBanachView
