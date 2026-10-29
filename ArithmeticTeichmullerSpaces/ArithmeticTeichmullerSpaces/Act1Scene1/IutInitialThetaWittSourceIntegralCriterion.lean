import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittGeometricInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittInverseRadiusOrbit

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-SOURCE-INTEGRAL-CRITERION
source: Joshi II `se:ff-rings`, the integral Witt source and the rho
norms underlying `pr:teichmuller-lift-A/B`.
fidelity: characterizes the original Ainf image in the original bounded
Witt localization by the simultaneous unit bounds at every radius.
Radii tending to zero force a positive-denominator numerator's constant
coefficient to vanish. Actual Witt division removes the p-denominator.
Radii tending to one then force all genuine digits, and hence every
Witt coefficient, into the original tilt integers. This constructs an
original Ainf witness without a Frobenius or representability hypothesis.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the criterion concerns the algebraic bounded
source. Integral approximation of arbitrary completed or annular elements
and the full Tate-kernel identity remain open. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittSourceIntegralCriterion

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion
open WittTeichmullerExpansion
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius

theorem numerator_prime_dvd_of_unit_bounds
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : ∀ ρ : Radius, InitialThetaWittRhoNorm.realValue D w ρ.val x ≤ 1)
    (m : ℕ) (y : FieldWitt D w)
    (hy : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ (m + 1) =
      algebraMap (FieldWitt D w) (Ambient D w) y) :
    (Arithmetic.residueChar w.1 : FieldWitt D w) ∣ y := by
  let ρ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hbound (s : Radius) : ‖digits (Arithmetic.residueChar w.1) y 0‖ ≤
      s.val.toReal ^ (m + 1) := by
    have h := (InitialThetaWittGeometricInterpolation.dividedTerm_le_realValue D w s x
      (m + 1) y hy 0).trans (hx s)
    simp only [pow_zero, mul_one] at h
    simpa only [one_mul] using (div_le_iff₀ (pow_pos
      (InitialThetaWittExponentialSeries.radius_toReal_pos s) (m + 1))).mp h
  have ht := (InitialThetaWittEigenRadiusDynamics.radiusOrbit_toReal_tendsto_zero D w ρ).pow (m + 1)
  rw [zero_pow (Nat.succ_ne_zero m)] at ht
  have hz : ‖digits (Arithmetic.residueChar w.1) y 0‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds ht
      (fun n => hbound (InitialThetaWittEigenRadiusDynamics.radiusOrbit D w ρ n))
  have hc : y.coeff 0 = 0 := by
    have hd := norm_eq_zero.mp (hz.antisymm (norm_nonneg _))
    simpa [digits] using hd
  exact Ideal.mem_span_singleton.mp
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero y).mpr hc)

theorem exists_witt_of_unit_bounds
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : ∀ ρ : Radius, InitialThetaWittRhoNorm.realValue D w ρ.val x ≤ 1)
    (m : ℕ) (y : FieldWitt D w)
    (hy : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) y) :
    ∃ b : FieldWitt D w, algebraMap (FieldWitt D w) (Ambient D w) b = toAmbient D w x := by
  induction m generalizing y with
  | zero => exact ⟨y, by simpa only [pow_zero, mul_one] using hy.symm⟩
  | succ m ih =>
    obtain ⟨b, hb⟩ := numerator_prime_dvd_of_unit_bounds D w x hx m y hy
    apply ih b
    have hp : (Arithmetic.residueChar w.1 : Ambient D w) ≠ 0 :=
      WittVector.FractionRing.p_nonzero (Arithmetic.residueChar w.1) (InitialThetaTiltField.Carrier D w)
    apply mul_right_cancel₀ hp
    calc
      _ = toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ (m + 1) := by
        rw [pow_succ, mul_assoc]
      _ = algebraMap (FieldWitt D w) (Ambient D w) y := hy
      _ = _ := by rw [hb, map_mul, map_natCast, mul_comm]

theorem digit_norm_le_one_of_unit_bounds
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : ∀ ρ : Radius, InitialThetaWittRhoNorm.realValue D w ρ.val x ≤ 1)
    (y : FieldWitt D w)
    (hy : algebraMap (FieldWitt D w) (Ambient D w) y = toAmbient D w x) (i : ℕ) :
    ‖digits (Arithmetic.residueChar w.1) y i‖ ≤ 1 := by
  let ρ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hpres : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ 0 =
      algebraMap (FieldWitt D w) (Ambient D w) y := by
    simpa only [pow_zero, mul_one] using hy.symm
  have ht := ((InitialThetaWittInverseRadiusOrbit.orbit_toReal_tendsto_one D w ρ).pow i).const_mul
    ‖digits (Arithmetic.residueChar w.1) y i‖
  have hle : ‖digits (Arithmetic.residueChar w.1) y i‖ * (1 : ℝ) ^ i ≤ 1 :=
    le_of_tendsto ht (Filter.Eventually.of_forall (fun n => by
      have h := (InitialThetaWittGeometricInterpolation.dividedTerm_le_realValue D w
        (InitialThetaWittInverseRadiusOrbit.orbit D w ρ n) x 0 y hpres i).trans
          (hx (InitialThetaWittInverseRadiusOrbit.orbit D w ρ n))
      simpa only [pow_zero, div_one] using h))
  simpa only [one_pow, mul_one] using hle

theorem exists_integral_of_unit_bounds
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : ∀ ρ : Radius, InitialThetaWittRhoNorm.realValue D w ρ.val x ≤ 1) :
    ∃ a : InitialThetaTiltFontaine.Ainf D w,
      InitialThetaBoundedWittLocalization.inclusion D w a = x := by
  let P := InitialThetaWittRhoValue.presentation D w x
  obtain ⟨y, hy⟩ := exists_witt_of_unit_bounds D w x hx P.exponent P.numerator P.relation
  have hc (i : ℕ) : ‖y.coeff i‖ ≤ 1 := by
    rw [(expands_iff_coeff _ _ _).mp (expands_digits (Arithmetic.residueChar w.1) y) i, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (digit_norm_le_one_of_unit_bounds D w x hx y hy i)
  let a : InitialThetaTiltFontaine.Ainf D w := WittVector.mk (Arithmetic.residueChar w.1)
    (fun i => ⟨y.coeff i, (LocalGeometricFontaine.mem_integerRing _ _).mpr (hc i)⟩)
  have ha : wittInclusion D w a = y := by
    apply WittVector.ext
    intro i
    rfl
  refine ⟨a, toAmbient_injective D w ?_⟩
  rw [toAmbient_inclusion]
  change algebraMap (FieldWitt D w) (Ambient D w) (wittInclusion D w a) = toAmbient D w x
  rw [ha, hy]

theorem integral_range_eq_unit_bounds :
    Set.range (InitialThetaBoundedWittLocalization.inclusion D w) =
      {x | ∀ ρ : Radius, InitialThetaWittRhoNorm.realValue D w ρ.val x ≤ 1} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩ ρ
    rw [← InitialThetaWittRhoCompletion.inclusion_norm D w ρ]
    exact InitialThetaWittRhoExpansion.norm_ainfMap_le_one D w ρ a
  · exact exists_integral_of_unit_bounds D w x

end
end JoshiTeich.Act1Scene1.InitialThetaWittSourceIntegralCriterion
