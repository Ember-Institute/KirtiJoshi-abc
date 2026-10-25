import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoCompletion
import Mathlib.Analysis.SpecificLimits.Basic

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-EXPANSION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, convergence
of Teichmuller expansions in a fixed rho completion of the bounded ring.
fidelity: integral Witt elements have remainder norm at most rho^(N+1).
Their genuine digit partial sums converge to their original image, and
localization denominators give convergent digit expansions for every
actual bounded Witt localization element. Original proofs; no reference
implementation copied and no analytic convergence law input.
boundary: Scene1/Derived; single-radius convergence does not yet construct
the common Frechet B or the Tate-log Frobenius eigenspace. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoExpansion

open JoshiTeich.Prologue
open InitialThetaBoundedWittExpansion InitialThetaBoundedWittLocalization
open WittTeichmullerExpansion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (ρ : InitialThetaWittRhoCompletion.Radius)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Ainf := InitialThetaTiltFontaine.Ainf D w
abbrev Completed := InitialThetaWittRhoCompletion.Completed D w ρ

def ainfMap : Ainf D w →+* Completed D w ρ :=
  (InitialThetaWittRhoCompletion.inclusion D w ρ).comp (inclusion D w)

theorem norm_ainfMap_le_one (a : Ainf D w) : ‖ainfMap D w ρ a‖ ≤ 1 := by
  rw [ainfMap, RingHom.comp_apply, InitialThetaWittRhoCompletion.inclusion_norm,
    InitialThetaWittRhoNorm.realValue,
    InitialThetaWittRhoValue.value_inclusion D w ρ.val ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne]
  have h := WittWeightedDigitNegation.value_map_le_one (Arithmetic.residueChar w.1)
    (LocalGeometricFontaine.integerRing (InitialThetaTiltField.Carrier D w))
    (LocalGeometricFontaine.mem_integerRing (InitialThetaTiltField.Carrier D w))
    ρ.val ρ.property.2.le a
  exact (ENNReal.toReal_mono ENNReal.one_ne_top h).trans_eq ENNReal.toReal_one

theorem norm_ainfMap_prime :
    ‖ainfMap D w ρ (Arithmetic.residueChar w.1)‖ = ρ.val.toReal := by
  change ‖InitialThetaWittRhoCompletion.inclusion D w ρ
    (inclusion D w (Arithmetic.residueChar w.1))‖ = _
  rw [map_natCast, InitialThetaWittRhoCompletion.inclusion_prime_norm]

def digitPartialSum (a : Ainf D w) (N : ℕ) : Ainf D w :=
  partialSum (Arithmetic.residueChar w.1) (digits (Arithmetic.residueChar w.1) a) N

theorem norm_remainder_le (a : Ainf D w) (N : ℕ) :
    ‖ainfMap D w ρ a - ainfMap D w ρ (digitPartialSum D w a N)‖ ≤ ρ.val.toReal ^ (N + 1) := by
  obtain ⟨q, hq⟩ := expands_digits (Arithmetic.residueChar w.1) a N
  rw [← map_sub]
  change ‖ainfMap D w ρ (a - partialSum _ _ N)‖ ≤ _
  rw [hq, map_mul, map_pow]
  calc
    _ ≤ ‖ainfMap D w ρ (Arithmetic.residueChar w.1) ^ (N + 1)‖ * ‖ainfMap D w ρ q‖ :=
      norm_mul_le _ _
    _ ≤ (‖ainfMap D w ρ (Arithmetic.residueChar w.1)‖ ^ (N + 1)) * 1 :=
      mul_le_mul (norm_pow_le' _ (Nat.succ_pos N)) (norm_ainfMap_le_one D w ρ q)
        (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ = _ := by rw [norm_ainfMap_prime, mul_one]

theorem tendsto_partial (a : Ainf D w) :
    Filter.Tendsto (fun N : ℕ => ainfMap D w ρ (digitPartialSum D w a N)) Filter.atTop
      (𝓝 (ainfMap D w ρ a)) := by
  have hr : ρ.val.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr ρ.property.2
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hr
  have hp' : Filter.Tendsto (fun N : ℕ => ρ.val.toReal ^ (N + 1)) Filter.atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using hp.mul_const ρ.val.toReal
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hp'
  simpa only [norm_sub_rev] using norm_remainder_le D w ρ a N

theorem exists_localized_expansion (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ∃ a : Ainf D w, ∃ b : InitialThetaBoundedWittLocalization.Ring D w,
      inclusion D w a * b = x ∧
      Filter.Tendsto
        (fun N : ℕ => InitialThetaWittRhoCompletion.inclusion D w ρ
          (inclusion D w (digitPartialSum D w a N) * b)) Filter.atTop
        (𝓝 (InitialThetaWittRhoCompletion.inclusion D w ρ x)) := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (denominator D w) x
  obtain ⟨u, hu⟩ := ((IsLocalization.Away.algebraMap_isUnit (denominator D w)
    (S := InitialThetaBoundedWittLocalization.Ring D w)).pow m)
  have hab : inclusion D w a * (u⁻¹ : _) = x := by
    change algebraMap (InitialThetaTiltFontaine.Ainf D w)
      (InitialThetaBoundedWittLocalization.Ring D w) a * (u⁻¹ : _) = x
    rw [← ha, ← hu, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨a, (u⁻¹ : _), hab, ?_⟩
  have h := (tendsto_partial D w ρ a).mul_const
    (InitialThetaWittRhoCompletion.inclusion D w ρ (u⁻¹ : _))
  simpa only [ainfMap, RingHom.comp_apply, ← map_mul, hab] using h

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoExpansion
