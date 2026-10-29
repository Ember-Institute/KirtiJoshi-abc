import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrobeniusWeight
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithmInjective

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-DIVISIBILITY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, the
Frobenius period space and its actual Tate period.
fidelity: division by a nonzero weight-m eigenvector lowers weight by m.
Negative-weight vanishing therefore bounds the power of the actual Tate
period dividing any nonzero integer-weight eigenvector. In particular,
the entire phi=p space has zero intersection with the ideal (t^2).
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; divisibility by t is not asserted for arbitrary
theta-kernel elements. The full Tate-kernel identity remains open. The
original common ring, scalar action and Prologue R5 are retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateDivisibility

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem quotient_weight (k m : ℤ) (a y : Carrier D w) (ha : a ≠ 0)
    (hea : frobeniusEquiv D w a =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ m) • a)
    (hey : frobeniusEquiv D w (a * y) =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • (a * y)) :
    frobeniusEquiv D w y =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ (k - m)) • y := by
  let p : Padic (Arithmetic.residueChar w.1) := Arithmetic.residueChar w.1
  have hp : p ≠ 0 := Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero
  have h : (p ^ m) • (a * frobeniusEquiv D w y) = (p ^ k) • (a * y) := by
    rw [map_mul, hea, smul_mul_assoc] at hey
    exact hey
  have h' := congrArg (fun z : Carrier D w => (p ^ m)⁻¹ • z) h
  rw [inv_smul_smul₀ (zpow_ne_zero m hp), smul_smul] at h'
  have hs : (p ^ m)⁻¹ * p ^ k = p ^ (k - m) := by
    rw [zpow_sub₀ hp, div_eq_mul_inv, mul_comm]
  rw [hs, ← mul_smul_comm] at h'
  exact (InitialThetaWittPrincipalIdealClosed.multiplication_isUniformEmbedding D w a ha).injective h'

theorem eq_zero_of_dvd_higher_weight (k m : ℤ) (hkm : k < m)
    (a x : Carrier D w) (ha : a ≠ 0)
    (hea : frobeniusEquiv D w a =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ m) • a)
    (hex : frobeniusEquiv D w x =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x)
    (hd : a ∣ x) : x = 0 := by
  obtain ⟨y, rfl⟩ := hd
  have hy := quotient_weight D w k m a y ha hea hex
  rw [InitialThetaWittFrobeniusWeight.eq_zero_of_negative_weight D w (k - m)
    (sub_neg.mpr hkm) y hy, mul_zero]

def tatePeriod : Carrier D w :=
  InitialThetaWittTateLogarithm.tateLog D w (InitialThetaCyclotomicTateTilt.generator D w)

theorem tatePeriod_ne_zero : tatePeriod D w ≠ 0 :=
  InitialThetaWittTateLogarithmInjective.canonical_tateLog_ne_zero D w

theorem tatePeriod_pow_ne_zero (m : ℕ) : tatePeriod D w ^ m ≠ 0 := by
  let ρ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  let N := InitialThetaWittRadiusFaithfulness.coordinateMulRingNorm D w ρ
  have ht : N (tatePeriod D w) ≠ 0 := by
    intro h
    exact tatePeriod_ne_zero D w
      ((InitialThetaWittRadiusFaithfulness.coordinateSeminorm_eq_zero_iff D w ρ _).mp h)
  intro h
  have hn := congrArg N h
  rw [map_pow, map_zero] at hn
  exact pow_ne_zero m ht hn

theorem tatePeriod_pow_equation (m : ℕ) :
    frobeniusEquiv D w (tatePeriod D w ^ m) =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ (m : ℤ)) •
        (tatePeriod D w ^ m) := by
  rw [map_pow, tatePeriod,
    InitialThetaWittTateFrobeniusEigen.frobenius_tateLog_eq_prime_mul, mul_pow,
    zpow_natCast, Algebra.smul_def, map_pow, map_natCast]

theorem eq_zero_of_tatePeriod_pow_dvd (k : ℤ) (m : ℕ) (hkm : k < (m : ℤ))
    (x : Carrier D w)
    (hex : frobeniusEquiv D w x =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x)
    (hd : tatePeriod D w ^ m ∣ x) : x = 0 :=
  eq_zero_of_dvd_higher_weight D w k m hkm _ x (tatePeriod_pow_ne_zero D w m)
    (tatePeriod_pow_equation D w m) hex hd

theorem tatePeriod_pow_dvd_weight_bound (k : ℤ) (m : ℕ) (x : Carrier D w) (hx : x ≠ 0)
    (hex : frobeniusEquiv D w x =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • x)
    (hd : tatePeriod D w ^ m ∣ x) : (m : ℤ) ≤ k := by
  by_contra h
  exact hx (eq_zero_of_tatePeriod_pow_dvd D w k m (lt_of_not_ge h) x hex hd)

theorem eigen_tatePeriod_sq_dvd_iff (x : InitialThetaWittEigenRadiusDynamics.Eigen D w) :
    tatePeriod D w ^ 2 ∣ x.val ↔ x = 0 := by
  constructor
  · intro hd
    apply Subtype.ext
    apply eq_zero_of_tatePeriod_pow_dvd D w 1 2 (by norm_num) x.val
    · have he : frobeniusEquiv D w x.val =
          (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x.val := x.property
      simpa only [zpow_one] using he
    · exact hd
  · rintro rfl
    exact dvd_zero _

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateDivisibility
