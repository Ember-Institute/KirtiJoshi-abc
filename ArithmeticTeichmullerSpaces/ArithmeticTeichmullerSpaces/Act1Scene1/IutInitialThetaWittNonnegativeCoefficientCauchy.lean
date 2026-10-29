import ArithmeticTeichmullerSpaces.Act1Scene1.WittLocalCoefficientBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittCompletedNonnegativeApproximation
import Mathlib.Topology.MetricSpace.Cauchy

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-NONNEGATIVE-COEFFICIENT-CAUCHY
source: Joshi II `se:ff-rings`, recovery of original Witt coefficients
from the rho completion used in `pr:teichmuller-lift-A/B`.
fidelity: unit-bounded rho-Cauchy original source elements with no
negative p-powers have Cauchy coefficients in the original tilt field.
For each finite coefficient head one fixed contracting Teichmuller
factor puts all approximants into the integral head ball. The actual
Witt addition and subtraction polynomials give a uniform difference
estimate. No integral coefficient hypothesis is imposed on the original
approximants. Original proofs; no reference implementation copied.
boundary: Scene1/Derived; integral limits and equality of their rho
images still require proof. Original source, norms and R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittNonnegativeCoefficientCauchy

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

private theorem radius_pos (ρ : Radius) : 0 < ρ.val.toReal :=
  ENNReal.toReal_pos ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne

private theorem radius_lt_one (ρ : Radius) : ρ.val.toReal < 1 := by
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
      ρ.property.2

theorem digit_norm_le_div (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) (y : FieldWitt D w)
    (hy : toAmbient D w x = algebraMap (FieldWitt D w) (Ambient D w) y)
    (i n : ℕ) (hin : i ≤ n) :
    ‖digits (Arithmetic.residueChar w.1) y i‖ ≤
      InitialThetaWittRhoNorm.realValue D w ρ.val x / ρ.val.toReal ^ n := by
  have hpres : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ 0 =
      algebraMap (FieldWitt D w) (Ambient D w) y := by simpa only [pow_zero, mul_one] using hy
  have h := InitialThetaWittGeometricInterpolation.dividedTerm_le_realValue D w ρ x 0 y hpres i
  simp only [pow_zero, div_one] at h
  apply (le_div_iff₀ (pow_pos (radius_pos ρ) n)).mpr
  have hp := pow_le_pow_of_le_one (radius_pos ρ).le
    (radius_lt_one ρ).le hin
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans h

private theorem scaled_coeff (r : InitialThetaTiltField.Carrier D w) (y : FieldWitt D w) (i : ℕ) :
    (WittVector.teichmuller (Arithmetic.residueChar w.1) r * y).coeff i =
      r ^ (Arithmetic.residueChar w.1 ^ i) * y.coeff i := by
  rw [(expands_iff_coeff _ _ _).mp
    (expands_teichmuller_mul (Arithmetic.residueChar w.1) r y _ (expands_digits _ y)) i,
    mul_pow, (expands_iff_coeff _ _ _).mp (expands_digits _ y) i]

theorem scaled_norm_coeff_sub_le (ρ : Radius) (n : ℕ)
    (r : InitialThetaTiltField.Carrier D w) (hr : ‖r‖ ≤ ρ.val.toReal ^ n)
    (a b : InitialThetaBoundedWittLocalization.Ring D w) (u v : FieldWitt D w)
    (hu : toAmbient D w a = algebraMap (FieldWitt D w) (Ambient D w) u)
    (hv : toAmbient D w b = algebraMap (FieldWitt D w) (Ambient D w) v)
    (ha : InitialThetaWittRhoNorm.realValue D w ρ.val a ≤ 1)
    (hb : InitialThetaWittRhoNorm.realValue D w ρ.val b ≤ 1) :
    ‖r‖ ^ (Arithmetic.residueChar w.1 ^ n) * ‖u.coeff n - v.coeff n‖ ≤
      InitialThetaWittRhoNorm.realValue D w ρ.val (a - b) / ρ.val.toReal ^ n := by
  let U := WittVector.teichmuller (Arithmetic.residueChar w.1) r * u
  let V := WittVector.teichmuller (Arithmetic.residueChar w.1) r * v
  have hρ := pow_pos (radius_pos ρ) n
  have hr1 : ‖r‖ ≤ 1 := hr.trans (pow_le_one₀
    (radius_pos ρ).le
      (radius_lt_one ρ).le)
  have hhead (x : InitialThetaBoundedWittLocalization.Ring D w) (y : FieldWitt D w)
      (hy : toAmbient D w x = algebraMap (FieldWitt D w) (Ambient D w) y)
      (hx : InitialThetaWittRhoNorm.realValue D w ρ.val x ≤ 1) (i : ℕ) (hi : i ≤ n) :
      ‖(WittVector.teichmuller (Arithmetic.residueChar w.1) r * y).coeff i‖ ≤ 1 := by
    rw [(expands_iff_coeff _ _ _).mp
      (expands_digits _ (WittVector.teichmuller (Arithmetic.residueChar w.1) r * y)) i,
      norm_pow, WittWeightedDigits.digits_teichmuller_mul, norm_mul]
    apply pow_le_one₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc
      _ ≤ ‖r‖ * (InitialThetaWittRhoNorm.realValue D w ρ.val x / ρ.val.toReal ^ n) :=
        mul_le_mul_of_nonneg_left (digit_norm_le_div D w ρ x y hy i n hi) (norm_nonneg _)
      _ ≤ ρ.val.toReal ^ n * (1 / ρ.val.toReal ^ n) :=
        mul_le_mul hr (div_le_div_of_nonneg_right hx hρ.le)
          (div_nonneg (InitialThetaWittRhoNorm.realValue_nonneg D w ρ.val x) hρ.le) hρ.le
      _ = 1 := by field_simp
  have hU := hhead a u hu ha
  have hV := hhead b v hv hb
  have hdiff (i : ℕ) (hi : i ≤ n) : ‖(U - V).coeff i‖ ≤ 1 :=
    WittLocalCoefficientBounds.norm_sub_coeff_le_one_of_head (Arithmetic.residueChar w.1) U V i
      (fun j hj => hU j (hj.trans hi)) (fun j hj => hV j (hj.trans hi))
  have hsub : toAmbient D w (a - b) = algebraMap (FieldWitt D w) (Ambient D w) (u - v) := by
    rw [map_sub, hu, hv, map_sub]
  have hsmall (i : ℕ) (hi : i ≤ n) : ‖(U - V).coeff i‖ ≤
      InitialThetaWittRhoNorm.realValue D w ρ.val (a - b) / ρ.val.toReal ^ n := by
    have hdi := hdiff i hi
    have he : U - V = WittVector.teichmuller (Arithmetic.residueChar w.1) r * (u - v) :=
      (mul_sub _ _ _).symm
    rw [he, (expands_iff_coeff _ _ _).mp (expands_digits _ _) i, norm_pow,
      WittWeightedDigits.digits_teichmuller_mul, norm_mul] at hdi ⊢
    have hbase := (pow_le_one_iff_of_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (pow_ne_zero i (Arithmetic.residueChar_prime w.1).ne_zero)).mp hdi
    calc
      _ ≤ ‖r‖ * ‖digits (Arithmetic.residueChar w.1) (u - v) i‖ := by
        simpa only [pow_one] using pow_le_pow_of_le_one
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbase
            (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero i (Arithmetic.residueChar_prime w.1).ne_zero))
      _ ≤ ‖digits (Arithmetic.residueChar w.1) (u - v) i‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hr1
      _ ≤ _ := digit_norm_le_div D w ρ (a - b) (u - v) hsub i n hi
  have h := WittLocalCoefficientBounds.norm_coeff_sub_le_of_head (Arithmetic.residueChar w.1)
    U V n hV hdiff _ (div_nonneg (InitialThetaWittRhoNorm.realValue_nonneg D w ρ.val _) hρ.le) hsmall
  change ‖(WittVector.teichmuller (Arithmetic.residueChar w.1) r * u).coeff n -
    (WittVector.teichmuller (Arithmetic.residueChar w.1) r * v).coeff n‖ ≤ _ at h
  rwa [scaled_coeff, scaled_coeff, ← mul_sub, norm_mul, norm_pow] at h

theorem cauchySeq_coeff (ρ : Radius)
    (a : ℕ → InitialThetaBoundedWittLocalization.Ring D w) (b : ℕ → FieldWitt D w)
    (hab : ∀ k, toAmbient D w (a k) = algebraMap (FieldWitt D w) (Ambient D w) (b k))
    (hb : ∀ k, InitialThetaWittRhoNorm.realValue D w ρ.val (a k) ≤ 1)
    (ha : CauchySeq (fun k => InitialThetaWittRhoCompletion.inclusion D w ρ (a k))) (n : ℕ) :
    CauchySeq (fun k => (b k).coeff n) := by
  have hρ := pow_pos (radius_pos ρ) n
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρ (InitialThetaBoundedWittLocalization.varpi_norm_pos_lt_one D w).2
  let r : InitialThetaTiltField.Carrier D w := (InitialThetaBoundedWittLocalization.varpi D w : _) ^ k
  have hr : ‖r‖ ≤ ρ.val.toReal ^ n := by
    change ‖(InitialThetaBoundedWittLocalization.varpi D w : InitialThetaTiltField.Carrier D w) ^ k‖ ≤ _
    rw [norm_pow]
    exact hk.le
  have hrpos : 0 < ‖r‖ := by
    change 0 < ‖(InitialThetaBoundedWittLocalization.varpi D w : InitialThetaTiltField.Carrier D w) ^ k‖
    rw [norm_pow]
    exact pow_pos (InitialThetaBoundedWittLocalization.varpi_norm_pos_lt_one D w).1 k
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ha
    ((ε * ‖r‖ ^ (Arithmetic.residueChar w.1 ^ n)) * ρ.val.toReal ^ n)
      (mul_pos (mul_pos hε (pow_pos hrpos _)) hρ)
  refine ⟨N, fun i hi j hj => ?_⟩
  have h := scaled_norm_coeff_sub_le D w ρ n r hr (a i) (a j) (b i) (b j)
    (hab i) (hab j) (hb i) (hb j)
  have hdist := hN i hi j hj
  rw [dist_eq_norm, ← map_sub, InitialThetaWittRhoCompletion.inclusion_norm] at hdist
  have hlt : InitialThetaWittRhoNorm.realValue D w ρ.val (a i - a j) / ρ.val.toReal ^ n <
      ε * ‖r‖ ^ (Arithmetic.residueChar w.1 ^ n) := (div_lt_iff₀ hρ).mpr hdist
  rw [dist_eq_norm]
  exact (mul_lt_mul_iff_right₀ (pow_pos hrpos _)).mp (by
    simpa only [mul_comm] using h.trans_lt hlt)

end
end JoshiTeich.Act1Scene1.InitialThetaWittNonnegativeCoefficientCauchy
