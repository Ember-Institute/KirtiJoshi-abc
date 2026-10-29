import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenRadiusDynamics
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittGeometricInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialSeries
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialLinearization
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FROBENIUS-WEIGHT
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, the
Frobenius eigenspaces in the Frechet period ring with its rho norms.
fidelity: three successive Frobenius radii and the proved geometric
interpolation inequality force every nonzero integer-weight eigenvector
of the actual common ring to have nonnegative weight. Negative-weight
solutions vanish on the entire carrier, without a bounded Witt or
principal logarithm representative. Original proofs; no reference code copied.
boundary: Scene1/Derived; full Tate-kernel classification and paper B
identity remain open. Original carrier, scalar action and R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrobeniusWeight

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittAllRadiusFrobenius
open InitialThetaWittRhoFrobeniusCompletion InitialThetaWittPadicScalarNorm
open InitialThetaWittExponentialSeries InitialThetaWittExponentialLinearization
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Radius := InitialThetaWittAllRadiusCompletion.Radius
abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

private def scalarNorm (ρ : Radius) : Padic (Arithmetic.residueChar w.1) →*₀ ℝ where
  toFun a := ‖completedPadicMap D w ρ a‖
  map_zero' := by rw [map_zero, norm_zero]
  map_one' := by rw [map_one, norm_one]
  map_mul' := norm_completedPadicMap_mul_scalar D w ρ

theorem norm_prime_zpow (ρ : Radius) (k : ℤ) :
    ‖completedPadicMap D w ρ ((Arithmetic.residueChar w.1 :
      Padic (Arithmetic.residueChar w.1)) ^ k)‖ = ρ.val.toReal ^ k := by
  change scalarNorm D w ρ ((Arithmetic.residueChar w.1 :
    Padic (Arithmetic.residueChar w.1)) ^ k) = _
  rw [map_zpow₀]
  change ‖completedPadicMap D w ρ (Arithmetic.residueChar w.1)‖ ^ k = _
  rw [map_natCast, InitialThetaWittPadicScalarContinuity.norm_completed_prime]

private theorem coordinate_pos (ρ : Radius) (x : Carrier D w) (hx : x ≠ 0) :
    0 < coordinateSeminorm D w ρ x := by
  exact lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm fun h =>
    hx ((InitialThetaWittRadiusFaithfulness.coordinateSeminorm_eq_zero_iff D w ρ x).mp h))

theorem log_coordinate_powered (ρ : Radius) (k : ℤ) (x : Carrier D w)
    (hx : x ≠ 0)
    (he : frobeniusEquiv D w x =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x) :
    Real.log (coordinateSeminorm D w (poweredRadius D w ρ) x) =
      (Arithmetic.residueChar w.1 : ℝ) * Real.log (coordinateSeminorm D w ρ x) -
        (k : ℝ) * Real.log (poweredRadius D w ρ).val.toReal := by
  have h := congrArg Real.log (coordinateSeminorm_frobenius D w ρ x)
  rw [he, coordinateSeminorm_smul, norm_prime_zpow,
    Real.log_mul (zpow_pos (InitialThetaWittExponentialSeries.radius_toReal_pos _) k).ne' (coordinate_pos D w _ x hx).ne',
    Real.log_zpow, Real.log_pow] at h
  linarith

private theorem powered_radius_weights (ρ : Radius) :
    (poweredRadius D w ρ).val.toReal =
      ρ.val.toReal ^ ((Arithmetic.residueChar w.1 : ℝ) / (Arithmetic.residueChar w.1 + 1)) *
        (poweredRadius D w (poweredRadius D w ρ)).val.toReal ^
          (1 / (Arithmetic.residueChar w.1 + 1 : ℝ)) := by
  let p : ℝ := Arithmetic.residueChar w.1
  have hp : p + 1 ≠ 0 := by dsimp [p]; positivity
  have hn : (poweredRadius D w ρ).val.toReal = ρ.val.toReal ^ Arithmetic.residueChar w.1 := by
    change (ρ.val ^ Arithmetic.residueChar w.1).toReal = _
    rw [ENNReal.toReal_pow]
  have hn' : (poweredRadius D w (poweredRadius D w ρ)).val.toReal =
      (ρ.val.toReal ^ Arithmetic.residueChar w.1) ^ Arithmetic.residueChar w.1 := by
    change ((poweredRadius D w ρ).val ^ Arithmetic.residueChar w.1).toReal = _
    rw [ENNReal.toReal_pow, hn]
  rw [hn, hn', ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (InitialThetaWittExponentialSeries.radius_toReal_pos ρ).le,
    ← Real.rpow_mul (InitialThetaWittExponentialSeries.radius_toReal_pos ρ).le,
    ← Real.rpow_add (InitialThetaWittExponentialSeries.radius_toReal_pos ρ)]
  congr 1
  change p = p / (p + 1) + (p * p) * (1 / (p + 1))
  field_simp
  ring

private theorem log_coordinate_convex (ρ : Radius) (x : Carrier D w) (hx : x ≠ 0) :
    ((Arithmetic.residueChar w.1 : ℝ) + 1) *
        Real.log (coordinateSeminorm D w (poweredRadius D w ρ) x) ≤
      (Arithmetic.residueChar w.1 : ℝ) * Real.log (coordinateSeminorm D w ρ x) +
        Real.log (coordinateSeminorm D w (poweredRadius D w (poweredRadius D w ρ)) x) := by
  let p : ℝ := Arithmetic.residueChar w.1
  have hp : 0 < p := Nat.cast_pos.mpr (Arithmetic.residueChar_prime w.1).pos
  have hp1 : 0 < p + 1 := by linarith
  have huv : p / (p + 1) + 1 / (p + 1) = 1 := by field_simp
  have h := InitialThetaWittGeometricInterpolation.coordinate_holder D w ρ
    (poweredRadius D w ρ) (poweredRadius D w (poweredRadius D w ρ))
    (p / (p + 1)) (1 / (p + 1)) (div_pos hp hp1) (div_pos zero_lt_one hp1)
    huv (powered_radius_weights D w ρ) x
  have hl := Real.log_le_log (coordinate_pos D w _ x hx) h
  rw [Real.log_mul (Real.rpow_pos_of_pos (coordinate_pos D w _ x hx) _).ne'
      (Real.rpow_pos_of_pos (coordinate_pos D w _ x hx) _).ne',
    Real.log_rpow (coordinate_pos D w _ x hx),
    Real.log_rpow (coordinate_pos D w _ x hx)] at hl
  calc
    _ ≤ (p + 1) * ((p / (p + 1)) * Real.log (coordinateSeminorm D w ρ x) +
        (1 / (p + 1)) * Real.log
          (coordinateSeminorm D w (poweredRadius D w (poweredRadius D w ρ)) x)) :=
      mul_le_mul_of_nonneg_left hl hp1.le
    _ = _ := by dsimp [p]; field_simp

private theorem nonnegative_weight_of_recurrence
    (p t k a b c : ℝ) (hp : 1 < p) (ht : t < 0)
    (h₁ : b = p * a - k * (p * t))
    (h₂ : c = p * b - k * (p * (p * t)))
    (hc : (p + 1) * b ≤ p * a + c) : 0 ≤ k := by
  have hcoef : 0 < p * (p - 1) * (-t) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hprod : 0 ≤ p * (p - 1) * (-t) * k := by
    rw [h₂, h₁] at hc
    nlinarith [hc]
  exact nonneg_of_mul_nonneg_right hprod hcoef

theorem weight_nonneg (k : ℤ) (x : Carrier D w) (hx : x ≠ 0)
    (he : frobeniusEquiv D w x =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x) :
    0 ≤ k := by
  let ρ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  have h₁ := log_coordinate_powered D w ρ k x hx he
  have h₂ := log_coordinate_powered D w (poweredRadius D w ρ) k x hx he
  have hpρ (r : Radius) : Real.log (poweredRadius D w r).val.toReal =
      (Arithmetic.residueChar w.1 : ℝ) * Real.log r.val.toReal := by
    have hpow : (poweredRadius D w r).val.toReal =
        r.val.toReal ^ Arithmetic.residueChar w.1 := by
      change (r.val ^ Arithmetic.residueChar w.1).toReal = _
      rw [ENNReal.toReal_pow]
    rw [hpow, Real.log_pow]
  rw [hpρ] at h₁
  rw [hpρ, hpρ] at h₂
  have h := nonnegative_weight_of_recurrence _ _ (k : ℝ) _ _ _
    (by exact_mod_cast (Arithmetic.residueChar_prime w.1).one_lt)
    (Real.log_neg (InitialThetaWittExponentialSeries.radius_toReal_pos ρ)
      (InitialThetaWittExponentialLinearization.radius_toReal_lt_one ρ)) h₁ h₂
    (log_coordinate_convex D w ρ x hx)
  exact_mod_cast h

theorem eq_zero_of_negative_weight (k : ℤ) (hk : k < 0) (x : Carrier D w)
    (he : frobeniusEquiv D w x =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x) :
    x = 0 := by
  by_contra hx
  exact (not_le_of_gt hk) (weight_nonneg D w k x hx he)

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrobeniusWeight
