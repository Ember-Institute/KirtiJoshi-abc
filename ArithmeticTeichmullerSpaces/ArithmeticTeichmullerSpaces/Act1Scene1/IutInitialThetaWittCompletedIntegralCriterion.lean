import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittCompletedIntegralCoefficients
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittIntegralImageTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRadiusFaithfulness

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-COMPLETED-INTEGRAL-CRITERION
source: Joshi II `se:ff-rings`, the integral Witt source in the Frechet
completion underlying `pr:teichmuller-lift-A/B`.
fidelity: proves that the original Ainf image in the original common
ring is exactly the simultaneous unit ball of all original rho norms.
The constructed nonnegative source approximants have integral coefficient
limits. A unit bound at a strictly larger radius gives uniform geometric
tail control at the target radius. Actual coefficient convergence handles
the finite head, identifies the original Ainf image, and faithfulness
gives equality in the whole original common ring. No source lift,
integral approximation or reconstruction law is assumed.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; annular elements are a distinct carrier and
are not identified with full common-ring elements. Their integral lift
and full Tate-kernel classification remain open. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittCompletedIntegralCriterion

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion WittTeichmullerExpansion
open InitialThetaWittAllRadiusCompletion
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

private theorem radius_pos (ρ : Radius) : 0 < ρ.val.toReal :=
  ENNReal.toReal_pos ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne

theorem realValue_le_of_digit_terms (ρ : Radius)
    (a : InitialThetaBoundedWittLocalization.Ring D w) (b : FieldWitt D w)
    (hab : toAmbient D w a = algebraMap (FieldWitt D w) (Ambient D w) b)
    (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i : ℕ, ‖digits (Arithmetic.residueChar w.1) b i‖ * ρ.val.toReal ^ i ≤ B) :
    InitialThetaWittRhoNorm.realValue D w ρ.val a ≤ B := by
  have hpres : toAmbient D w a * (Arithmetic.residueChar w.1 : Ambient D w) ^ 0 =
      algebraMap (FieldWitt D w) (Ambient D w) b := by simpa only [pow_zero, mul_one] using hab
  have hv : InitialThetaWittRhoValue.value D w ρ.val a ≤ ENNReal.ofReal B := by
    rw [InitialThetaWittRhoValue.value_eq_of_presentation D w ρ.val ρ.property.1.ne'
      (ρ.property.2.trans ENNReal.one_lt_top).ne a 0 b hpres, pow_zero, div_one]
    apply iSup_le
    intro i
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top (ρ.property.2.trans ENNReal.one_lt_top).ne)) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal hB] using h i
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hv).trans_eq (ENNReal.toReal_ofReal hB)

theorem tendsto_norm_digits_sub (b : ℕ → FieldWitt D w) (c : FieldWitt D w)
    (hb : ∀ i : ℕ, Filter.Tendsto (fun k => (b k).coeff i) Filter.atTop (𝓝 (c.coeff i))) (i : ℕ) :
    Filter.Tendsto (fun k => ‖digits (Arithmetic.residueChar w.1) (b k - c) i‖)
      Filter.atTop (𝓝 0) := by
  have ht := WittCoefficientConvergence.tendsto_sub_coeff (Arithmetic.residueChar w.1) b c hb i
  have he (k : ℕ) : ‖(b k - c).coeff i‖ =
      ‖digits (Arithmetic.residueChar w.1) (b k - c) i‖ ^ (Arithmetic.residueChar w.1 ^ i) := by
    rw [(expands_iff_coeff _ _ _).mp (expands_digits _ (b k - c)) i, norm_pow]
  apply (PositivePowerCalibration.tendsto_rpow_zero_iff Filter.atTop
    (fun k => ‖digits (Arithmetic.residueChar w.1) (b k - c) i‖) (fun _ => norm_nonneg _)
    ((Arithmetic.residueChar w.1 ^ i : ℕ) : ℝ)
    (Nat.cast_pos.mpr (pow_pos (Arithmetic.residueChar_prime w.1).pos i))).mp
  simpa only [Real.rpow_natCast, ← he, norm_zero] using ht.norm

theorem tendsto_inclusion_of_coefficients (ρ t : Radius) (hρt : ρ.val < t.val)
    (a : ℕ → InitialThetaBoundedWittLocalization.Ring D w) (b : ℕ → FieldWitt D w)
    (hab : ∀ k, toAmbient D w (a k) = algebraMap (FieldWitt D w) (Ambient D w) (b k))
    (hunit : ∀ᶠ k in Filter.atTop, InitialThetaWittRhoNorm.realValue D w t.val (a k) ≤ 1)
    (c : InitialThetaTiltFontaine.Ainf D w)
    (hc : ∀ i : ℕ, Filter.Tendsto (fun k => (b k).coeff i) Filter.atTop
      (𝓝 (c.coeff i : InitialThetaTiltField.Carrier D w))) :
    Filter.Tendsto (fun k => InitialThetaWittRhoCompletion.inclusion D w ρ (a k))
      Filter.atTop (𝓝 (InitialThetaWittRhoExpansion.ainfMap D w ρ c)) := by
  let d := InitialThetaBoundedWittLocalization.inclusion D w c
  have hsub (k : ℕ) : toAmbient D w (a k - d) =
      algebraMap (FieldWitt D w) (Ambient D w) (b k - wittInclusion D w c) := by
    rw [map_sub, hab k, map_sub, toAmbient_inclusion]
    rfl
  have htunit : ∀ᶠ k in Filter.atTop, InitialThetaWittRhoNorm.realValue D w t.val (a k - d) ≤ 1 := by
    filter_upwards [hunit] with k hk
    have h := InitialThetaWittRhoNorm.realValue_add_le_max D w t.val t.property.1.ne' t.property.2.le
      (a k) (-d)
    rw [← sub_eq_add_neg, InitialThetaWittRhoNorm.realValue_neg D w t.val t.property.1.ne' t.property.2.le] at h
    have hd : InitialThetaWittRhoNorm.realValue D w t.val d ≤ 1 := by
      rw [← InitialThetaWittRhoCompletion.inclusion_norm D w t]
      exact InitialThetaWittRhoExpansion.norm_ainfMap_le_one D w t c
    exact h.trans (max_le hk hd)
  have hratio0 : 0 ≤ ρ.val.toReal / t.val.toReal := (div_pos (radius_pos ρ) (radius_pos t)).le
  have hratio1 : ρ.val.toReal / t.val.toReal < 1 := (div_lt_one (radius_pos t)).mpr
    ((ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne
      (t.property.2.trans ENNReal.one_lt_top).ne).mpr hρt)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Filter.Tendsto (fun N : ℕ => (ρ.val.toReal / t.val.toReal) ^ (N + 1))
      Filter.atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).mul_const
      (ρ.val.toReal / t.val.toReal)
    simpa only [pow_succ, zero_mul] using h
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  have hhead : ∀ᶠ k in Filter.atTop, ∀ i ∈ Finset.Iic N,
      ‖digits (Arithmetic.residueChar w.1) (b k - wittInclusion D w c) i‖ * ρ.val.toReal ^ i ≤ ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have h := (tendsto_norm_digits_sub D w b (wittInclusion D w c) hc i).mul_const (ρ.val.toReal ^ i)
    rw [zero_mul] at h
    exact (h.eventually (gt_mem_nhds (half_pos hε))).mono (fun _ h => h.le)
  filter_upwards [htunit, hhead] with k hk hh
  have hnorm : InitialThetaWittRhoNorm.realValue D w ρ.val (a k - d) ≤ ε / 2 := by
    apply realValue_le_of_digit_terms D w ρ (a k - d) _ (hsub k) _ (half_pos hε).le
    intro i
    by_cases hi : i ≤ N
    · exact hh i (Finset.mem_Iic.mpr hi)
    · have hd := InitialThetaWittNonnegativeCoefficientCauchy.digit_norm_le_div
        D w t (a k - d) _ (hsub k) i i le_rfl
      calc
        _ ≤ (1 / t.val.toReal ^ i) * ρ.val.toReal ^ i :=
          mul_le_mul_of_nonneg_right (hd.trans
            (div_le_div_of_nonneg_right hk (pow_nonneg (radius_pos t).le i)))
              (pow_nonneg (radius_pos ρ).le i)
        _ = (ρ.val.toReal / t.val.toReal) ^ i := by rw [div_pow]; ring
        _ ≤ (ρ.val.toReal / t.val.toReal) ^ (N + 1) :=
          pow_le_pow_of_le_one hratio0 hratio1.le (by omega)
        _ ≤ ε / 2 := hN.le
  have he : InitialThetaWittRhoCompletion.inclusion D w ρ (a k) -
      InitialThetaWittRhoExpansion.ainfMap D w ρ c =
        InitialThetaWittRhoCompletion.inclusion D w ρ (a k - d) := (map_sub _ _ _).symm
  simpa only [dist_zero_right, norm_norm, he, InitialThetaWittRhoCompletion.inclusion_norm,
    Real.norm_eq_abs, abs_of_nonneg (InitialThetaWittRhoNorm.realValue_nonneg D w ρ.val (a k - d))]
    using hnorm.trans_lt (half_lt_self hε)

theorem exists_integral_of_unit_bounds (ρ : Radius) (x : Carrier D w)
    (hx : ∀ r : Radius, ‖evaluate D w r x‖ ≤ 1) :
    ∃ c : InitialThetaTiltFontaine.Ainf D w,
      InitialThetaWittAllRadiusExpansion.ainfMap D w c = x := by
  obtain ⟨a, b, c, hab, hunit, ha, hc⟩ :=
    InitialThetaWittCompletedIntegralCoefficients.exists_completed_integral_coefficients D w ρ x hx
  obtain ⟨tval, hρt, ht1⟩ := exists_between ρ.property.2
  let t : Radius := ⟨tval, ρ.property.1.trans hρt, ht1⟩
  have hbase : ∀ᶠ k in Filter.atTop, t.val ≤ (InitialThetaWittInverseRadiusOrbit.orbit D w ρ k).val := by
    have ht : t.val.toReal < 1 := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (t.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr t.property.2
    filter_upwards [(InitialThetaWittInverseRadiusOrbit.orbit_toReal_tendsto_one D w ρ).eventually
      (lt_mem_nhds ht)] with k hk
    exact (ENNReal.toReal_le_toReal (t.property.2.trans ENNReal.one_lt_top).ne
      ((InitialThetaWittInverseRadiusOrbit.orbit D w ρ k).property.2.trans ENNReal.one_lt_top).ne).mp hk.le
  have hu : ∀ᶠ k in Filter.atTop, InitialThetaWittRhoNorm.realValue D w t.val (a k) ≤ 1 := by
    filter_upwards [hbase] with k hk
    exact (InitialThetaWittCompletedIntegralCoefficients.realValue_mono_of_nonnegative
      D w t _ hk (a k) (b k) (hab k)).trans (hunit k)
  have hlimit := tendsto_inclusion_of_coefficients D w ρ t hρt a b hab hu c hc
  refine ⟨c, InitialThetaWittRadiusFaithfulness.evaluate_injective D w ρ ?_⟩
  exact tendsto_nhds_unique hlimit ha

theorem integral_range_eq_unit_bounds (ρ : Radius) :
    Set.range (InitialThetaWittAllRadiusExpansion.ainfMap D w) =
      {x : Carrier D w | ∀ r : Radius, ‖evaluate D w r x‖ ≤ 1} := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩ r
    exact InitialThetaWittRhoExpansion.norm_ainfMap_le_one D w r c
  · exact exists_integral_of_unit_bounds D w ρ x

end
end JoshiTeich.Act1Scene1.InitialThetaWittCompletedIntegralCriterion
