import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittScalarCalibration
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPadicComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoUltrametric
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-NORMALIZED-SEMINORMS
source: Joshi II `se:ff-rings`, the Frechet Q_p algebra topology
defined by the multiplicative rho norms.
fidelity: positive powers of the original coordinate norms are genuine
Q_p seminorms for the standard p-adic scalar norm. They are multiplicative,
ultrametric, continuous and recover the original coordinate norms by
inverse powers. Proves WithSeminorms for the existing topology and for
the canonical source completion, without changing either topology.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; full paper period/BK comparisons remain open.
The calibrated seminorms are related explicitly to the original rho norms.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittNormalizedSeminorms

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittScalarCalibration
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def value (ρ : Radius) (x : Carrier D w) : ℝ :=
  InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x ^ exponent D w ρ

theorem value_nonneg (ρ : Radius) (x : Carrier D w) : 0 ≤ value D w ρ x :=
  Real.rpow_nonneg (apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) x) _

theorem value_add_le_max (ρ : Radius) (x y : Carrier D w) :
    value D w ρ (x + y) ≤ max (value D w ρ x) (value D w ρ y) := by
  have h : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (x + y) ≤
      max (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x)
        (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ y) := by
    change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (x + y)‖ ≤ _
    rw [map_add]
    exact InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _
  exact (Real.rpow_le_rpow
    (apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) (x + y))
    h (exponent_pos D w ρ).le).trans_eq
      (PositivePowerCalibration.rpow_max _ _ _
        (apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) x)
        (apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) y)
        (exponent_pos D w ρ).le)

theorem value_add_le (ρ : Radius) (x y : Carrier D w) :
    value D w ρ (x + y) ≤ value D w ρ x + value D w ρ y :=
  (value_add_le_max D w ρ x y).trans
    (max_le (le_add_of_nonneg_right (value_nonneg D w ρ y))
      (le_add_of_nonneg_left (value_nonneg D w ρ x)))

theorem value_smul (ρ : Radius) (a : Padic (Arithmetic.residueChar w.1)) (x : Carrier D w) :
    value D w ρ (a • x) = ‖a‖ * value D w ρ x := by
  unfold value
  rw [InitialThetaWittPadicScalarNorm.coordinateSeminorm_smul,
    Real.mul_rpow (norm_nonneg _)
      (apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) x), completedPadicMap_rpow]

def seminorm (ρ : Radius) : Seminorm (Padic (Arithmetic.residueChar w.1)) (Carrier D w) :=
  Seminorm.of (value D w ρ) (value_add_le D w ρ) (value_smul D w ρ)

theorem seminorm_apply (ρ : Radius) (x : Carrier D w) :
    seminorm D w ρ x = InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x ^ exponent D w ρ := rfl

theorem seminorm_mul (ρ : Radius) (x y : Carrier D w) :
    seminorm D w ρ (x * y) = seminorm D w ρ x * seminorm D w ρ y := by
  change value D w ρ (x * y) = value D w ρ x * value D w ρ y
  unfold value
  rw [InitialThetaWittMultiplicativeNorm.coordinateSeminorm_mul,
    Real.mul_rpow (apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) x)
      (apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) y)]

theorem seminorm_one (ρ : Radius) : seminorm D w ρ 1 = 1 := by
  change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ 1‖ ^ exponent D w ρ = 1
  rw [map_one, norm_one, Real.one_rpow]

theorem seminorm_isNonarchimedean (ρ : Radius) : IsNonarchimedean (seminorm D w ρ) :=
  value_add_le_max D w ρ

theorem seminorm_continuous (ρ : Radius) : Continuous (seminorm D w ρ) :=
  (InitialThetaWittAllRadiusCompletion.coordinateSeminorm_continuous D w ρ).rpow_const
    (fun _ => Or.inr (exponent_pos D w ρ).le)

theorem recover_coordinate (ρ : Radius) (x : Carrier D w) :
    seminorm D w ρ x ^ (exponent D w ρ)⁻¹ =
      InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x :=
  Real.rpow_rpow_inv (apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) x)
    (exponent_pos D w ρ).ne'

theorem tendsto_zero_iff_seminorms {ι : Type*} (l : Filter ι) (f : ι → Carrier D w) :
    Filter.Tendsto f l (𝓝 0) ↔ ∀ ρ : Radius,
      Filter.Tendsto (fun i => seminorm D w ρ (f i)) l (𝓝 0) := by
  rw [InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates]
  simp only [map_zero]
  apply forall_congr'
  intro ρ
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact (PositivePowerCalibration.tendsto_rpow_zero_iff l
    (fun i => ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (f i)‖)
    (fun _ => norm_nonneg _) (exponent D w ρ) (exponent_pos D w ρ)).symm

theorem withSeminorms : WithSeminorms (seminorm D w) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  apply le_antisymm
  · refine le_iInf (fun ρ => ?_)
    have h := (seminorm_continuous D w ρ).tendsto (0 : Carrier D w)
    rw [map_zero] at h
    exact h.le_comap
  · have h := (tendsto_zero_iff_seminorms D w
      (⨅ ρ : Radius, Filter.comap (seminorm D w ρ) (𝓝 (0 : ℝ))) id).mpr
        (fun ρ => Filter.tendsto_comap.mono_left (iInf_le _ ρ))
    exact Filter.tendsto_id'.mp h

instance carrierPolynormable : PolynormableSpace (Padic (Arithmetic.residueChar w.1)) (Carrier D w) :=
  (withSeminorms D w).toPolynormableSpace

theorem exists_seminorm_ne_zero (x : Carrier D w) (hx : x ≠ 0) :
    ∃ ρ : Radius, seminorm D w ρ x ≠ 0 := (withSeminorms D w).separating_of_T1 x hx

def completedSeminorm (ρ : Radius) : Seminorm (Padic (Arithmetic.residueChar w.1))
    (InitialThetaWittFrechetComparison.Completed D w) :=
  (seminorm D w ρ).comp (InitialThetaWittFrechetPadicComparison.algEquiv D w).toLinearMap

theorem completedSeminorm_apply (ρ : Radius) (x : InitialThetaWittFrechetComparison.Completed D w) :
    completedSeminorm D w ρ x =
      ‖InitialThetaWittFrechetComparison.radiusMap D w ρ x‖ ^ exponent D w ρ := rfl

theorem completedSeminorm_originalInclusion (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    completedSeminorm D w ρ (InitialThetaWittFrechetComparison.originalInclusion D w x) =
      InitialThetaWittRhoNorm.realValue D w ρ.val x ^ exponent D w ρ := by
  rw [completedSeminorm_apply, InitialThetaWittFrechetComparison.norm_radiusMap_originalInclusion]

theorem completed_withSeminorms : WithSeminorms (completedSeminorm D w) := by
  have h : Topology.IsInducing (InitialThetaWittFrechetPadicComparison.algEquiv D w).toLinearMap :=
    (InitialThetaWittFrechetComparison.uniformEquiv D w).toHomeomorph.isInducing
  exact h.withSeminorms (withSeminorms D w)

instance completedPolynormable : PolynormableSpace (Padic (Arithmetic.residueChar w.1))
    (InitialThetaWittFrechetComparison.Completed D w) :=
  (completed_withSeminorms D w).toPolynormableSpace

end
end JoshiTeich.Act1Scene1.InitialThetaWittNormalizedSeminorms
