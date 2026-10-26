import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenRadiusTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-BANACH
source: Joshi II `se:ff-rings` and the B^{phi=p} Banach space in the
period sequence in the proof of `pr:teichmuller-lift-A`.
fidelity: restricts the proved standard-Q_p calibrated seminorm at the
original theta radius to the entire actual phi=p subspace. It is a norm
and defines the original uniformity. The normed group explicitly retains
that uniformity, and its original scalar action is a standard Q_p normed
space action. The existing completeness is retained on this same carrier.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no new period carrier or completion is used.
Full principal-log representation and period/BK identity remain open.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenBanach

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittEigenRadiusDynamics InitialThetaWittEigenRadiusTopology
open scoped Topology Uniformity
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def calibratedSeminorm : Seminorm (Padic (Arithmetic.residueChar w.1)) (Eigen D w) :=
  (InitialThetaWittNormalizedSeminorms.seminorm D w (InitialThetaWittThetaBound.radius D w)).comp
    (InitialThetaWittAdditiveTatePeriod.frobeniusPrimeSubmodule D w).subtype

theorem calibratedSeminorm_eq_zero_iff (x : Eigen D w) :
    calibratedSeminorm D w x = 0 ↔ x = 0 := by
  change InitialThetaWittNormalizedSeminorms.seminorm D w
    (InitialThetaWittThetaBound.radius D w) x.val = 0 ↔ x = 0
  rw [InitialThetaWittRadiusFaithfulness.seminorm_eq_zero_iff]
  constructor
  · exact fun h => Subtype.ext h
  · rintro rfl
    rfl

theorem tendsto_zero_iff_calibratedSeminorm {ι : Type*} (l : Filter ι) (f : ι → Eigen D w) :
    Filter.Tendsto f l (𝓝 0) ↔ Filter.Tendsto (fun i => calibratedSeminorm D w (f i)) l (𝓝 0) := by
  rw [tendsto_zero_iff_fixedCoordinate D w l f (InitialThetaWittThetaBound.radius D w)]
  exact (PositivePowerCalibration.tendsto_rpow_zero_iff l
    (fun i => coordinateSeminorm D w (InitialThetaWittThetaBound.radius D w) (f i).val)
    (fun i => apply_nonneg _ _)
    (InitialThetaWittScalarCalibration.exponent D w (InitialThetaWittThetaBound.radius D w))
    (InitialThetaWittScalarCalibration.exponent_pos D w (InitialThetaWittThetaBound.radius D w))).symm

theorem withCalibratedSeminorm : WithSeminorms (fun _ : Unit => calibratedSeminorm D w) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, iInf_const]
  apply le_antisymm
  · have h := (tendsto_zero_iff_calibratedSeminorm D w (𝓝 (0 : Eigen D w)) id).mp Filter.tendsto_id
    exact h.le_comap
  · have h := (tendsto_zero_iff_calibratedSeminorm D w
      (Filter.comap (calibratedSeminorm D w) (𝓝 (0 : ℝ))) id).mpr Filter.tendsto_comap
    exact Filter.tendsto_id'.mp h

theorem uniformSpace_eq_calibrated :
    (inferInstance : UniformSpace (Eigen D w)) =
      (calibratedSeminorm D w).toSeminormedAddCommGroup.toUniformSpace := by
  have h := (SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf
    (fun _ : Unit => calibratedSeminorm D w)).mp (withCalibratedSeminorm D w)
  simpa only [iInf_const] using h

def calibratedNorm : AddGroupNorm (Eigen D w) where
  __ := (calibratedSeminorm D w).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' x := (calibratedSeminorm_eq_zero_iff D w x).mp

theorem uniformity_eq_calibrated : 𝓤 (Eigen D w) =
    𝓤[(calibratedNorm D w).toNormedAddCommGroup.toUniformSpace] :=
  congrArg (fun U : UniformSpace (Eigen D w) => 𝓤[U]) (uniformSpace_eq_calibrated D w)

instance eigenNormedAddCommGroup : NormedAddCommGroup (Eigen D w) :=
  { (calibratedNorm D w).toNormedAddCommGroup with
    toMetricSpace := (calibratedNorm D w).toNormedAddCommGroup.toMetricSpace.replaceUniformity
      (uniformity_eq_calibrated D w) }

theorem norm_eq_calibrated (x : Eigen D w) : ‖x‖ = calibratedSeminorm D w x := rfl

theorem norm_eq_coordinate_power (x : Eigen D w) :
    ‖x‖ = coordinateSeminorm D w (InitialThetaWittThetaBound.radius D w) x.val ^
      InitialThetaWittScalarCalibration.exponent D w (InitialThetaWittThetaBound.radius D w) := rfl

instance eigenNormedSpace : NormedSpace (Padic (Arithmetic.residueChar w.1)) (Eigen D w) where
  toModule := inferInstance
  norm_smul_le a x := (map_smul_eq_mul (calibratedSeminorm D w) a x).le

theorem eigen_banach_complete : CompleteSpace (Eigen D w) :=
  InitialThetaWittEigenRadiusTopology.eigenComplete D w

theorem norm_add_le_max (x y : Eigen D w) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  InitialThetaWittNormalizedSeminorms.value_add_le_max D w
    (InitialThetaWittThetaBound.radius D w) x.val y.val

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenBanach
