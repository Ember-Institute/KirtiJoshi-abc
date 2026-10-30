import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAnnularFiniteCoordinateDensity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittMultiplicativeNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithm
import Mathlib.Analysis.SpecificLimits.Normed

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ANNULAR-INTEGRAL-OBSTRUCTION
source: Joshi II `se:ff-rings`, the bounded Witt source and its annular
rho norms preceding `pr:teichmuller-lift-A`.
fidelity: for every positive inner radius, constructs an original
bounded source element [varpi]^n/p. It has norm less than one at every
annular radius but is not an image of original Ainf. Its norm is
|varpi|^n/r, which exceeds one at a sufficiently small original radius.
Faithfulness of the original source inclusion at one annular radius
then excludes any exact integral lift of the annular element itself.
A geometric series gives an actual annular unit 1-[varpi]^n/p whose
value and inverse both have norm one at every annular radius. This
unit still has no integral lift.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this excludes integral reconstruction from
generic annular unit bounds. No Frobenius-power equation is imposed
on this example. Recognition of actual annular eigen exponentials
still requires their additional equations. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAnnularIntegralObstruction

open JoshiTeich.Prologue
open InitialThetaWittAnnularExponential InitialThetaWittAnnularFiniteCoordinateDensity
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

private theorem fraction_norm (r : Radius) (n : ℕ)
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : x * (Arithmetic.residueChar w.1 : InitialThetaBoundedWittLocalization.Ring D w) =
      InitialThetaBoundedWittLocalization.inclusion D w
        (InitialThetaBoundedWittLocalization.teichVarpi D w ^ n)) :
    InitialThetaWittRhoNorm.realValue D w r.val x =
      ‖InitialThetaBoundedWittLocalization.varpi D w‖ ^ n / r.val.toReal := by
  have h := congrArg (fun y => ‖InitialThetaWittRhoCompletion.inclusion D w r y‖) hx
  rw [map_mul, norm_mul, InitialThetaWittRhoCompletion.inclusion_prime_norm] at h
  change ‖InitialThetaWittRhoCompletion.inclusion D w r x‖ * r.val.toReal =
    ‖InitialThetaWittRhoExpansion.ainfMap D w r
      (InitialThetaBoundedWittLocalization.teichVarpi D w ^ n)‖ at h
  rw [map_pow, norm_pow, InitialThetaBoundedWittLocalization.teichVarpi,
    InitialThetaWittTateLogarithm.norm_ainf_teichmuller,
    InitialThetaWittRhoCompletion.inclusion_norm] at h
  exact (eq_div_iff (ENNReal.toReal_pos r.property.1.ne'
    (r.property.2.trans ENNReal.one_lt_top).ne).ne').mpr h

theorem exists_unit_bounded_nonintegral_source (ρ : Radius) :
    ∃ x : InitialThetaBoundedWittLocalization.Ring D w,
      (∀ r : AnnularRadius ρ, InitialThetaWittRhoNorm.realValue D w r.val.val x < 1) ∧
      ¬ ∃ a : InitialThetaTiltFontaine.Ainf D w,
        InitialThetaBoundedWittLocalization.inclusion D w a = x := by
  have hv := InitialThetaBoundedWittLocalization.varpi_norm_pos_lt_one D w
  have hρ : 0 < ρ.val.toReal := ENNReal.toReal_pos ρ.property.1.ne'
    (ρ.property.2.trans ENNReal.one_lt_top).ne
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hv.1.le hv.2).eventually
    (gt_mem_nhds hρ)).exists
  obtain ⟨u, hu⟩ := InitialThetaBoundedWittLocalization.prime_isUnit D w
  have hp : (u : InitialThetaBoundedWittLocalization.Ring D w) =
      (Arithmetic.residueChar w.1 : InitialThetaBoundedWittLocalization.Ring D w) := by
    rw [hu, map_natCast]
  let q := InitialThetaBoundedWittLocalization.inclusion D w
    (InitialThetaBoundedWittLocalization.teichVarpi D w ^ n)
  let x : InitialThetaBoundedWittLocalization.Ring D w :=
    ((u⁻¹ : (InitialThetaBoundedWittLocalization.Ring D w)ˣ) :
      InitialThetaBoundedWittLocalization.Ring D w) * q
  have hx : x * (Arithmetic.residueChar w.1 : InitialThetaBoundedWittLocalization.Ring D w) = q := by
    rw [← hp]
    change ((u⁻¹ : (InitialThetaBoundedWittLocalization.Ring D w)ˣ) :
      InitialThetaBoundedWittLocalization.Ring D w) * q * ↑u = q
    rw [mul_right_comm, Units.inv_mul, one_mul]
  have hnorm (r : Radius) := fraction_norm D w r n x hx
  refine ⟨x, ?_, ?_⟩
  · intro r
    rw [hnorm]
    apply (div_lt_one (ENNReal.toReal_pos r.val.property.1.ne'
      (r.val.property.2.trans ENNReal.one_lt_top).ne)).mpr
    exact hn.trans_le ((ENNReal.toReal_le_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne
      (r.val.property.2.trans ENNReal.one_lt_top).ne).mpr r.property)
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm⟩ := ((InitialThetaWittEigenRadiusDynamics.radiusOrbit_toReal_tendsto_zero D w ρ).eventually
      (gt_mem_nhds (pow_pos hv.1 n))).exists
    let r := InitialThetaWittEigenRadiusDynamics.radiusOrbit D w ρ m
    have hb := InitialThetaWittRhoExpansion.norm_ainfMap_le_one D w r a
    change ‖InitialThetaWittRhoCompletion.inclusion D w r
      (InitialThetaBoundedWittLocalization.inclusion D w a)‖ ≤ 1 at hb
    rw [ha, InitialThetaWittRhoCompletion.inclusion_norm, hnorm] at hb
    exact (not_le_of_gt ((one_lt_div (ENNReal.toReal_pos r.property.1.ne'
      (r.property.2.trans ENNReal.one_lt_top).ne)).mpr hm)) hb

theorem exists_unit_bounded_without_integral_lift (ρ : Radius) :
    ∃ x : Carrier D w ρ, (∀ r : AnnularRadius ρ, ‖evaluate D w ρ r x‖ ≤ 1) ∧
      ¬ ∃ a : InitialThetaTiltFontaine.Ainf D w,
        ∀ r : AnnularRadius ρ, evaluate D w ρ r x = InitialThetaWittRhoExpansion.ainfMap D w r.val a := by
  obtain ⟨x, hx, hnot⟩ := exists_unit_bounded_nonintegral_source D w ρ
  refine ⟨sourceInclusion D w ρ x, ?_, ?_⟩
  · intro r
    change ‖InitialThetaWittRhoCompletion.inclusion D w r.val x‖ ≤ 1
    rw [InitialThetaWittRhoCompletion.inclusion_norm]
    exact (hx r).le
  · rintro ⟨a, ha⟩
    apply hnot
    refine ⟨a, InitialThetaWittRhoCompletion.inclusion_injective D w ρ ?_⟩
    exact (ha ⟨ρ, le_rfl⟩).symm

theorem exists_unit_without_integral_lift (ρ : Radius) :
    ∃ u : (Carrier D w ρ)ˣ,
      (∀ r : AnnularRadius ρ, ‖evaluate D w ρ r u.val‖ ≤ 1 ∧
        ‖evaluate D w ρ r (u⁻¹).val‖ ≤ 1) ∧
      ¬ ∃ a : InitialThetaTiltFontaine.Ainf D w,
        ∀ r : AnnularRadius ρ, evaluate D w ρ r u.val = InitialThetaWittRhoExpansion.ainfMap D w r.val a := by
  obtain ⟨x, hx, hnot⟩ := exists_unit_bounded_nonintegral_source D w ρ
  let z := sourceInclusion D w ρ x
  have hz (r : AnnularRadius ρ) : ‖evaluate D w ρ r z‖ < 1 := by
    change ‖InitialThetaWittRhoCompletion.inclusion D w r.val x‖ < 1
    rw [InitialThetaWittRhoCompletion.inclusion_norm]
    exact hx r
  let g : Product D w ρ := fun r => ∑' n : ℕ, evaluate D w ρ r z ^ n
  have hs : HasSum (fun n : ℕ => z.val ^ n) g := by
    apply Pi.hasSum.mpr
    intro r
    exact (summable_geometric_of_norm_lt_one (hz r)).hasSum
  have hg : g ∈ closedSubring D w ρ := by
    apply (Subring.isClosed_topologicalClosure (diagonal D w ρ).range).mem_of_tendsto hs
    exact Filter.Eventually.of_forall (fun s : Finset ℕ =>
      (closedSubring D w ρ).sum_mem (fun n _ => (closedSubring D w ρ).pow_mem z.property n))
  let y : Carrier D w ρ := ⟨g, hg⟩
  have hzy : (1 - z) * y = 1 := by
    apply ext D w ρ
    intro r
    change (1 - evaluate D w ρ r z) * (∑' n : ℕ, evaluate D w ρ r z ^ n) = 1
    exact mul_neg_geom_series _ (hz r)
  let u : (Carrier D w ρ)ˣ := ⟨1 - z, y, hzy, (mul_comm _ _).trans hzy⟩
  refine ⟨u, ?_, ?_⟩
  · intro r
    have hn : ‖evaluate D w ρ r u.val‖ = 1 := by
      change ‖1 - evaluate D w ρ r z‖ = 1
      have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (x := (1 : InitialThetaWittRhoCompletion.Completed D w r.val))
        (y := -evaluate D w ρ r z) (by simpa only [norm_one, norm_neg] using (hz r).ne')
      simpa only [← sub_eq_add_neg, norm_one, norm_neg, max_eq_left (hz r).le] using h
    have hi := congrArg (fun a => ‖evaluate D w ρ r a‖) u.val_inv
    rw [map_mul, map_one, norm_mul, norm_one, hn, one_mul] at hi
    exact ⟨hn.le, hi.le⟩
  · rintro ⟨a, ha⟩
    apply hnot
    refine ⟨1 - a, InitialThetaWittRhoCompletion.inclusion_injective D w ρ ?_⟩
    change InitialThetaWittRhoExpansion.ainfMap D w ρ (1 - a) =
      InitialThetaWittRhoCompletion.inclusion D w ρ x
    rw [map_sub, map_one, ← ha ⟨ρ, le_rfl⟩]
    change 1 - (1 - InitialThetaWittRhoCompletion.inclusion D w ρ x) = _
    ring

end
end JoshiTeich.Act1Scene1.InitialThetaWittAnnularIntegralObstruction
