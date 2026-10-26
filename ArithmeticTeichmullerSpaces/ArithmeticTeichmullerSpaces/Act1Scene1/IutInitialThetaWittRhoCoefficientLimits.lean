import ArithmeticTeichmullerSpaces.Act1Scene1.WittIntegralCoefficientBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTeichmullerRecognition
import Mathlib.Topology.MetricSpace.Cauchy

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-COEFFICIENT-LIMITS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, recovery of
original integral Witt representatives from rho-Cauchy approximations.
fidelity: proves the actual coefficient difference estimate
norm(a_n-b_n)<=rho^(-n)*norm(i_rho(a-b)). Every rho-Cauchy sequence of
original Ainf elements therefore has convergent coefficients in the
original complete tilt field. Their limits remain integral and define
one actual Witt vector; no new coefficient or completion is introduced.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; coefficient recovery does not alone prove
convergence of rho images or closedness of the integral image. These
remain separate steps; full period representation remains open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoCoefficientLimits

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open WittTeichmullerExpansion InitialThetaBoundedWittExpansion
open InitialThetaWittExponentialSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem digit_norm_le_one (a : InitialThetaTiltFontaine.Ainf D w) (i : ℕ) :
    ‖digits (Arithmetic.residueChar w.1) a i‖ ≤ 1 :=
  (LocalGeometricFontaine.mem_integerRing _ _).mp (digits (Arithmetic.residueChar w.1) a i).property

theorem digit_norm_mul_pow_le (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w) (i : ℕ) :
    ‖digits (Arithmetic.residueChar w.1) a i‖ * ρ.val.toReal ^ i ≤
      ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a‖ := by
  have hd := digits_unique (Arithmetic.residueChar w.1) (wittInclusion D w a)
    (fun n => algebraMap (InitialThetaTiltIntegers.Integers D w)
      (InitialThetaTiltField.Carrier D w) (digits (Arithmetic.residueChar w.1) a n))
    (expands_map (Arithmetic.residueChar w.1) _ a _ (expands_digits _ a))
  have h := InitialThetaWittGeometricInterpolation.dividedTerm_le_realValue D w ρ
    (InitialThetaBoundedWittLocalization.inclusion D w a) 0 (wittInclusion D w a)
    (by simpa only [pow_zero, mul_one, ambientInclusion, RingHom.comp_apply] using toAmbient_inclusion D w a) i
  rw [← congrFun hd i] at h
  have hn : ‖algebraMap (InitialThetaTiltIntegers.Integers D w) (InitialThetaTiltField.Carrier D w)
      (digits (Arithmetic.residueChar w.1) a i)‖ = ‖digits (Arithmetic.residueChar w.1) a i‖ := rfl
  rw [InitialThetaWittRhoExpansion.ainfMap, RingHom.comp_apply, InitialThetaWittRhoCompletion.inclusion_norm]
  simpa only [pow_zero, div_one, hn] using h

theorem coeff_norm_mul_pow_le (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w) (i : ℕ) :
    ‖a.coeff i‖ * ρ.val.toReal ^ i ≤ ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a‖ := by
  have hc := (expands_iff_coeff (Arithmetic.residueChar w.1) a _).mp (expands_digits _ a) i
  rw [hc, norm_pow]
  have hpow := pow_le_pow_of_le_one (norm_nonneg _) (digit_norm_le_one D w a i)
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero i (Arithmetic.residueChar_prime w.1).ne_zero))
  exact (mul_le_mul_of_nonneg_right (by simpa only [pow_one] using hpow)
    (pow_nonneg (radius_toReal_pos ρ).le i)).trans (digit_norm_mul_pow_le D w ρ a i)

theorem coeff_norm_le_div (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w) (i n : ℕ) (hin : i ≤ n) :
    ‖a.coeff i‖ ≤ ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a‖ / ρ.val.toReal ^ n := by
  apply (le_div_iff₀ (pow_pos (radius_toReal_pos ρ) n)).mpr
  have hp := pow_le_pow_of_le_one (radius_toReal_pos ρ).le
    (InitialThetaWittExponentialLinearization.radius_toReal_lt_one ρ).le hin
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (coeff_norm_mul_pow_le D w ρ a i)

theorem norm_coeff_sub_le (ρ : Radius) (a b : InitialThetaTiltFontaine.Ainf D w) (n : ℕ) :
    ‖(a.coeff n : InitialThetaTiltField.Carrier D w) - (b.coeff n : InitialThetaTiltField.Carrier D w)‖ ≤
      ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (a - b)‖ / ρ.val.toReal ^ n := by
  have hb : ∀ i, ‖(wittInclusion D w b).coeff i‖ ≤ 1 := by
    intro i
    change ‖(b.coeff i : InitialThetaTiltField.Carrier D w)‖ ≤ 1
    exact (LocalGeometricFontaine.mem_integerRing _ _).mp (b.coeff i).property
  have hd : ∀ i, ‖(wittInclusion D w a - wittInclusion D w b).coeff i‖ ≤ 1 := by
    intro i
    rw [← map_sub]
    change ‖((a - b).coeff i : InitialThetaTiltField.Carrier D w)‖ ≤ 1
    exact (LocalGeometricFontaine.mem_integerRing _ _).mp ((a - b).coeff i).property
  apply WittIntegralCoefficientBounds.norm_coeff_sub_le (Arithmetic.residueChar w.1)
    (wittInclusion D w a) (wittInclusion D w b) hb hd n _
      (div_nonneg (norm_nonneg _) (pow_pos (radius_toReal_pos ρ) n).le)
  intro i hin
  rw [← map_sub]
  have hn : ‖(wittInclusion D w (a - b)).coeff i‖ = ‖(a - b).coeff i‖ := rfl
  rw [hn]
  exact coeff_norm_le_div D w ρ (a - b) i n hin

theorem cauchySeq_coeff (ρ : Radius) (a : ℕ → InitialThetaTiltFontaine.Ainf D w)
    (ha : CauchySeq (fun m => InitialThetaWittRhoExpansion.ainfMap D w ρ (a m))) (i : ℕ) :
    CauchySeq (fun m => ((a m).coeff i : InitialThetaTiltField.Carrier D w)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ha (ε * ρ.val.toReal ^ i)
    (mul_pos hε (pow_pos (radius_toReal_pos ρ) i))
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  apply (norm_coeff_sub_le D w ρ (a m) (a n) i).trans_lt
  apply (div_lt_iff₀ (pow_pos (radius_toReal_pos ρ) i)).mpr
  simpa only [dist_eq_norm, ← map_sub] using hN m hm n hn

theorem exists_coefficient_limit (ρ : Radius) (a : ℕ → InitialThetaTiltFontaine.Ainf D w)
    (ha : CauchySeq (fun m => InitialThetaWittRhoExpansion.ainfMap D w ρ (a m))) :
    ∃ b : InitialThetaTiltFontaine.Ainf D w, ∀ i : ℕ,
      Filter.Tendsto (fun m => ((a m).coeff i : InitialThetaTiltField.Carrier D w)) Filter.atTop
        (𝓝 (b.coeff i : InitialThetaTiltField.Carrier D w)) := by
  have hlim : ∀ i : ℕ, ∃ c : InitialThetaTiltField.Carrier D w,
      Filter.Tendsto (fun m => ((a m).coeff i : InitialThetaTiltField.Carrier D w)) Filter.atTop (𝓝 c) :=
    fun i => cauchySeq_tendsto_of_complete (cauchySeq_coeff D w ρ a ha i)
  choose c hc using hlim
  have hi : ∀ i : ℕ, c i ∈ InitialThetaTiltIntegers.Integers D w := by
    intro i
    apply (LocalGeometricFontaine.mem_integerRing _ _).mpr
    apply le_of_tendsto (hc i).norm
    exact Filter.Eventually.of_forall (fun m =>
      (LocalGeometricFontaine.mem_integerRing _ _).mp ((a m).coeff i).property)
  exact ⟨WittVector.mk (Arithmetic.residueChar w.1) (fun i => ⟨c i, hi i⟩), hc⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoCoefficientLimits
