import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittGeometricInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNormalizedSeminorms

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RADIUS-FAITHFULNESS
source: Joshi II `se:ff-rings`, the multiplicative rho norms on the
Frechet completion of the bounded Witt period source.
fidelity: positive geometric interpolation propagates a zero at one
radius to every radius. Joint separation then proves that each radius
evaluation is injective and each coordinate is a multiplicative norm.
The same faithfulness holds for the native source completion and its
standard Q_p calibrated seminorms. No topology is replaced.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; full paper carrier and period/BK comparisons
remain open. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRadiusFaithfulness

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusCompletion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem coordinate_zero_of_zero (s r : Radius) (x : Carrier D w)
    (hs : coordinateSeminorm D w s x = 0) : coordinateSeminorm D w r x = 0 := by
  apply le_antisymm _ (apply_nonneg (coordinateSeminorm D w r) x)
  rcases lt_trichotomy r.val s.val with hrs | heq | hsr
  · obtain ⟨a, ha0, har⟩ := exists_between r.property.1
    let a' : Radius := ⟨a, ha0, har.trans r.property.2⟩
    obtain ⟨u, v, _, hv, _, h⟩ :=
      InitialThetaWittGeometricInterpolation.exists_coordinate_holder D w a' r s har hrs
    have hx := h x
    rw [hs, Real.zero_rpow hv.ne', mul_zero] at hx
    exact hx
  · have h : r = s := Subtype.ext heq
    simpa only [h] using hs.le
  · obtain ⟨b, hrb, hb1⟩ := exists_between r.property.2
    let b' : Radius := ⟨b, r.property.1.trans hrb, hb1⟩
    obtain ⟨u, v, hu, _, _, h⟩ :=
      InitialThetaWittGeometricInterpolation.exists_coordinate_holder D w s r b' hsr hrb
    have hx := h x
    rw [hs, Real.zero_rpow hu.ne', zero_mul] at hx
    exact hx

theorem coordinateSeminorm_eq_zero_iff (ρ : Radius) (x : Carrier D w) :
    coordinateSeminorm D w ρ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact (coordinates_separate_zero D w x).mp (fun r => coordinate_zero_of_zero D w ρ r x hx)
  · rintro rfl
    exact map_zero _

theorem evaluate_injective (ρ : Radius) : Function.Injective (evaluate D w ρ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (coordinateSeminorm_eq_zero_iff D w ρ (x - y)).mp
  change ‖evaluate D w ρ (x - y)‖ = 0
  rw [map_sub, hxy, sub_self, norm_zero]

def coordinateMulRingNorm (ρ : Radius) : MulRingNorm (Carrier D w) where
  __ := InitialThetaWittMultiplicativeNorm.coordinateMulSeminorm D w ρ
  eq_zero_of_map_eq_zero' x := (coordinateSeminorm_eq_zero_iff D w ρ x).mp

theorem coordinateMulRingNorm_apply (ρ : Radius) (x : Carrier D w) :
    coordinateMulRingNorm D w ρ x = coordinateSeminorm D w ρ x := rfl

theorem seminorm_eq_zero_iff (ρ : Radius) (x : Carrier D w) :
    InitialThetaWittNormalizedSeminorms.seminorm D w ρ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply (coordinateSeminorm_eq_zero_iff D w ρ x).mp
    rw [← InitialThetaWittNormalizedSeminorms.recover_coordinate D w ρ x, hx,
      Real.zero_rpow (inv_pos.mpr (InitialThetaWittScalarCalibration.exponent_pos D w ρ)).ne']
  · rintro rfl
    exact map_zero _

theorem radiusMap_injective (ρ : Radius) :
    Function.Injective (InitialThetaWittFrechetComparison.radiusMap D w ρ) :=
  (evaluate_injective D w ρ).comp (InitialThetaWittFrechetComparison.ringEquiv D w).injective

theorem radiusMap_norm_eq_zero_iff (ρ : Radius)
    (x : InitialThetaWittFrechetComparison.Completed D w) :
    ‖InitialThetaWittFrechetComparison.radiusMap D w ρ x‖ = 0 ↔ x = 0 := by
  rw [norm_eq_zero]
  constructor
  · intro hx
    apply radiusMap_injective D w ρ
    rw [hx, map_zero]
  · rintro rfl
    exact map_zero _

theorem completedSeminorm_eq_zero_iff (ρ : Radius)
    (x : InitialThetaWittFrechetComparison.Completed D w) :
    InitialThetaWittNormalizedSeminorms.completedSeminorm D w ρ x = 0 ↔ x = 0 := by
  change InitialThetaWittNormalizedSeminorms.seminorm D w ρ
    (InitialThetaWittFrechetPadicComparison.algEquiv D w x) = 0 ↔ x = 0
  rw [seminorm_eq_zero_iff]
  constructor
  · intro hx
    apply (InitialThetaWittFrechetPadicComparison.algEquiv D w).injective
    rw [hx, map_zero]
  · rintro rfl
    exact map_zero _

end
end JoshiTeich.Act1Scene1.InitialThetaWittRadiusFaithfulness
