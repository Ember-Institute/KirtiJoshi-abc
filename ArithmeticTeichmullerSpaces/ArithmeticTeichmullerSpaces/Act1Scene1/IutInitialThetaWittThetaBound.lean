import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittGeometricInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittMultiplicativeNorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-THETA-BOUND
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, the
canonical untilt evaluation on the completed period ring.
fidelity: at rho equal to the original untilt norm of p, genuine Witt
digit sums converge under the original Fontaine map. Their term bounds
prove contraction by the actual rho norm. The same bound extends to
the original bounded localization using its actual denominator.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; extension to the completion is a separate
consumer. No new input law or paper identity is assumed. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittThetaBound

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion WittTeichmullerExpansion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Untilt := InitialThetaCanonicalGeometricFontaine.coefficientField D w
abbrev Ainf := InitialThetaTiltFontaine.Ainf D w

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def radius : InitialThetaWittRhoCompletion.Radius :=
  ⟨ENNReal.ofReal ‖(Arithmetic.residueChar w.1 : Untilt D w)‖,
    ENNReal.ofReal_pos.mpr (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.1,
    by simpa only [← ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr
        (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2⟩

theorem radius_toReal : (radius D w).val.toReal = ‖(Arithmetic.residueChar w.1 : Untilt D w)‖ :=
  ENNReal.toReal_ofReal (norm_nonneg _)

def integralEvaluation : Ainf D w →+* Untilt D w :=
  (LocalGeometricFontaine.integerRing (Untilt D w)).subtype.comp (InitialThetaTiltFontaine.theta D w)

theorem integralEvaluation_norm_le_one (a : Ainf D w) : ‖integralEvaluation D w a‖ ≤ 1 :=
  (LocalGeometricFontaine.mem_integerRing _ _).mp (InitialThetaTiltFontaine.theta D w a).property

theorem integralEvaluation_teichmuller_norm (a : InitialThetaTiltIntegers.Integers D w) :
    ‖integralEvaluation D w (WittVector.teichmuller (Arithmetic.residueChar w.1) a)‖ = ‖a‖ :=
  InitialThetaTiltFontaine.theta_teichmuller_norm D w a

theorem norm_remainder_le (a : Ainf D w) (N : ℕ) :
    ‖integralEvaluation D w a - integralEvaluation D w
      (InitialThetaWittRhoExpansion.digitPartialSum D w a N)‖ ≤
      ‖(Arithmetic.residueChar w.1 : Untilt D w)‖ ^ (N + 1) := by
  obtain ⟨q, hq⟩ := expands_digits (Arithmetic.residueChar w.1) a N
  rw [← map_sub]
  change ‖integralEvaluation D w (a - partialSum _ _ N)‖ ≤ _
  rw [hq, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (integralEvaluation_norm_le_one D w q)

theorem tendsto_partial (a : Ainf D w) :
    Filter.Tendsto (fun N : ℕ => integralEvaluation D w
      (InitialThetaWittRhoExpansion.digitPartialSum D w a N)) Filter.atTop
      (𝓝 (integralEvaluation D w a)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (norm_nonneg (Arithmetic.residueChar w.1 : Untilt D w))
    (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2
  have hp' : Filter.Tendsto (fun N : ℕ =>
      ‖(Arithmetic.residueChar w.1 : Untilt D w)‖ ^ (N + 1)) Filter.atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using hp.mul_const ‖(Arithmetic.residueChar w.1 : Untilt D w)‖
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hp'
  simpa only [norm_sub_rev] using norm_remainder_le D w a N

theorem digit_le_realValue (a : Ainf D w) (i : ℕ) :
    ‖digits (Arithmetic.residueChar w.1) a i‖ * (radius D w).val.toReal ^ i ≤
      InitialThetaWittRhoNorm.realValue D w (radius D w).val
        (InitialThetaBoundedWittLocalization.inclusion D w a) := by
  have hd := digits_unique (Arithmetic.residueChar w.1) (wittInclusion D w a)
    (fun n => algebraMap (InitialThetaTiltIntegers.Integers D w)
      (InitialThetaTiltField.Carrier D w) (digits (Arithmetic.residueChar w.1) a n))
    (expands_map (Arithmetic.residueChar w.1) _ a _ (expands_digits _ a))
  have h := InitialThetaWittGeometricInterpolation.dividedTerm_le_realValue D w (radius D w)
    (InitialThetaBoundedWittLocalization.inclusion D w a) 0 (wittInclusion D w a)
    (by simpa only [pow_zero, mul_one, ambientInclusion, RingHom.comp_apply] using toAmbient_inclusion D w a) i
  rw [← congrFun hd i] at h
  have hn : ‖algebraMap (InitialThetaTiltIntegers.Integers D w)
      (InitialThetaTiltField.Carrier D w) (digits (Arithmetic.residueChar w.1) a i)‖ =
      ‖digits (Arithmetic.residueChar w.1) a i‖ := rfl
  simpa only [pow_zero, div_one, hn] using h

theorem norm_partial_le_realValue (a : Ainf D w) (N : ℕ) :
    ‖integralEvaluation D w (InitialThetaWittRhoExpansion.digitPartialSum D w a N)‖ ≤
      InitialThetaWittRhoNorm.realValue D w (radius D w).val
        (InitialThetaBoundedWittLocalization.inclusion D w a) := by
  let M := InitialThetaWittRhoNorm.realValue D w (radius D w).val
    (InitialThetaBoundedWittLocalization.inclusion D w a)
  have ht (i : ℕ) : ‖integralEvaluation D w
      (WittVector.teichmuller (Arithmetic.residueChar w.1) (digits (Arithmetic.residueChar w.1) a i) *
        (Arithmetic.residueChar w.1 : Ainf D w) ^ i)‖ ≤ M := by
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, integralEvaluation_teichmuller_norm]
    simpa only [radius_toReal] using digit_le_realValue D w a i
  have hs (s : Finset ℕ) : ‖∑ i ∈ s, integralEvaluation D w
      (WittVector.teichmuller (Arithmetic.residueChar w.1) (digits (Arithmetic.residueChar w.1) a i) *
        (Arithmetic.residueChar w.1 : Ainf D w) ^ i)‖ ≤ M := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, norm_zero] using InitialThetaWittRhoNorm.realValue_nonneg D w (radius D w).val _
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ht i) ih)
  simpa only [InitialThetaWittRhoExpansion.digitPartialSum, partialSum, map_sum] using hs (Finset.Iic N)

theorem integralEvaluation_norm_le_realValue (a : Ainf D w) :
    ‖integralEvaluation D w a‖ ≤ InitialThetaWittRhoNorm.realValue D w (radius D w).val
      (InitialThetaBoundedWittLocalization.inclusion D w a) :=
  le_of_tendsto (tendsto_partial D w a).norm
    (Filter.Eventually.of_forall (norm_partial_le_realValue D w a))

theorem denominator_norm :
    ‖integralEvaluation D w (InitialThetaBoundedWittLocalization.denominator D w)‖ =
      ‖(Arithmetic.residueChar w.1 : Untilt D w)‖ ^ 2 := by
  rw [InitialThetaBoundedWittLocalization.denominator, map_mul, map_natCast, norm_mul,
    InitialThetaBoundedWittLocalization.teichVarpi, integralEvaluation_teichmuller_norm,
    InitialThetaBoundedWittLocalization.varpi, InitialThetaTiltFontaine.integralLift_norm, pow_two]
  rfl

theorem denominator_realValue :
    InitialThetaWittRhoNorm.realValue D w (radius D w).val
      (InitialThetaBoundedWittLocalization.inclusion D w (InitialThetaBoundedWittLocalization.denominator D w)) =
      ‖integralEvaluation D w (InitialThetaBoundedWittLocalization.denominator D w)‖ := by
  rw [← InitialThetaWittRhoCompletion.inclusion_norm]
  change ‖InitialThetaWittRhoExpansion.ainfMap D w (radius D w)
    (InitialThetaBoundedWittLocalization.denominator D w)‖ = _
  rw [InitialThetaBoundedWittLocalization.denominator, map_mul, norm_mul, map_mul, norm_mul,
    InitialThetaWittRhoExpansion.norm_ainfMap_prime, map_natCast,
    InitialThetaBoundedWittLocalization.teichVarpi,
    InitialThetaWittTateLogarithm.norm_ainf_teichmuller, integralEvaluation_teichmuller_norm, radius_toReal]

theorem evaluation_norm_le (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ‖InitialThetaBoundedWittLocalization.evaluation D w x‖ ≤
      InitialThetaWittRhoNorm.realValue D w (radius D w).val x := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (InitialThetaBoundedWittLocalization.denominator D w) x
  have he (b : Ainf D w) : InitialThetaBoundedWittLocalization.evaluation D w
      (InitialThetaBoundedWittLocalization.inclusion D w b) = integralEvaluation D w b :=
    InitialThetaBoundedWittLocalization.evaluation_inclusion D w b
  have hEval := congrArg (fun z => ‖InitialThetaBoundedWittLocalization.evaluation D w z‖) ha
  change ‖InitialThetaBoundedWittLocalization.evaluation D w
    (x * InitialThetaBoundedWittLocalization.inclusion D w
      (InitialThetaBoundedWittLocalization.denominator D w) ^ m)‖ =
      ‖InitialThetaBoundedWittLocalization.evaluation D w (InitialThetaBoundedWittLocalization.inclusion D w a)‖ at hEval
  rw [map_mul, map_pow, norm_mul, norm_pow, he, he] at hEval
  have hRho := congrArg (InitialThetaWittRhoNorm.realValue D w (radius D w).val) ha
  change InitialThetaWittRhoNorm.realValue D w (radius D w).val
    (x * InitialThetaBoundedWittLocalization.inclusion D w
      (InitialThetaBoundedWittLocalization.denominator D w) ^ m) =
      InitialThetaWittRhoNorm.realValue D w (radius D w).val (InitialThetaBoundedWittLocalization.inclusion D w a) at hRho
  rw [← InitialThetaWittRhoCompletion.inclusion_norm] at hRho
  rw [map_mul, map_pow, norm_mul, norm_pow, InitialThetaWittRhoCompletion.inclusion_norm,
    InitialThetaWittRhoCompletion.inclusion_norm, denominator_realValue] at hRho
  have hb := integralEvaluation_norm_le_realValue D w a
  rw [← hEval, ← hRho] at hb
  have hd : 0 < ‖integralEvaluation D w (InitialThetaBoundedWittLocalization.denominator D w)‖ ^ m := by
    rw [denominator_norm]
    exact pow_pos (pow_pos (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.1 _) _
  nlinarith

end
end JoshiTeich.Act1Scene1.InitialThetaWittThetaBound
