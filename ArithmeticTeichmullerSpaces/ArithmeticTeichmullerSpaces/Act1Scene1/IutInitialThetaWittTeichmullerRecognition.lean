import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusTeichmullerRigidity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAnnularExponential

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TEICHMULLER-RECOGNITION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, integral
Witt representatives of multiplicative-formal-group periods.
fidelity: proves injectivity and Frobenius compatibility of each actual
Ainf radius map. A completed Frobenius-power equation pulls back to
the original Witt vector and forces it to be its zeroth coefficient's
Teichmuller lift. Applies this to any actual integral representative of
the constructed annular eigen exponential, using its proved equation.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the theorem consumes an actual integral
representative, whose existence is not assumed globally or asserted.
Full period representation remains open. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTeichmullerRecognition

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittEigenRadiusDynamics InitialThetaWittInverseRadiusOrbit
open InitialThetaWittExponentialSeries InitialThetaWittExponentialLinearization
open InitialThetaWittRhoFrobeniusCompletion InitialThetaWittRhoFrobeniusEquiv
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem ainfMap_injective (ρ : Radius) : Function.Injective (InitialThetaWittRhoExpansion.ainfMap D w ρ) :=
  (InitialThetaWittRhoCompletion.inclusion_injective D w ρ).comp
    (InitialThetaBoundedWittLocalization.inclusion_injective D w)

theorem completedFrobenius_ainfMap (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w) :
    completedEquiv D w ρ (InitialThetaWittRhoExpansion.ainfMap D w ρ a) =
      InitialThetaWittRhoExpansion.ainfMap D w (poweredRadius D w ρ) (WittVector.frobenius a) := by
  change completedEquiv D w ρ (InitialThetaWittRhoCompletion.inclusion D w ρ
    (InitialThetaBoundedWittLocalization.inclusion D w a)) = _
  rw [completedEquiv_inclusion]
  change InitialThetaWittRhoCompletion.inclusion D w (poweredRadius D w ρ)
    (InitialThetaBoundedWittLocalization.frobenius D w
      (InitialThetaBoundedWittLocalization.inclusion D w a)) = _
  rw [InitialThetaBoundedWittLocalization.frobenius_inclusion]
  rfl

theorem eq_teichmuller_of_completed_equation (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w)
    (ha : completedEquiv D w ρ (InitialThetaWittRhoExpansion.ainfMap D w ρ a) =
      InitialThetaWittRhoExpansion.ainfMap D w (poweredRadius D w ρ) a ^ Arithmetic.residueChar w.1) :
    a = WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0) := by
  apply WittFrobeniusTeichmullerRigidity.eq_teichmuller_of_frobenius_eq_pow
  apply ainfMap_injective D w (poweredRadius D w ρ)
  rw [map_pow]
  exact (completedFrobenius_ainfMap D w ρ a).symm.trans ha

theorem base_le_inverse_radius (ρ : Radius) : ρ.val ≤ (orbit D w ρ 1).val := by
  have hp := pow_le_pow_of_le_one (radius_toReal_pos (orbit D w ρ 1)).le
    (radius_toReal_lt_one (orbit D w ρ 1)).le
    (Nat.one_le_iff_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  rw [pow_one, orbit_toReal_pow D w ρ 0, orbit_zero] at hp
  exact (ENNReal.toReal_le_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne
    ((orbit D w ρ 1).property.2.trans ENNReal.one_lt_top).ne).mp hp

theorem eq_teichmuller_of_annular_exponential_lift (ρ : Radius) (z : Eigen D w)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z.val‖ < s.val.val.toReal)
    (a : InitialThetaTiltFontaine.Ainf D w)
    (ha : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ z.val hz) =
          InitialThetaWittRhoExpansion.ainfMap D w s.val a) :
    a = WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0) := by
  let s : InitialThetaWittAnnularExponential.AnnularRadius ρ :=
    ⟨orbit D w ρ 1, base_le_inverse_radius D w ρ⟩
  have he : poweredRadius D w s.val = ρ := by
    change poweredRadius D w (orbit D w ρ (0 + 1)) = ρ
    rw [powered_orbit_succ, orbit_zero]
  have hs : ρ.val ≤ (poweredRadius D w s.val).val := by rw [he]
  apply eq_teichmuller_of_completed_equation D w s.val a
  have h := InitialThetaWittAnnularExponential.eigen_annular_frobenius D w ρ z hz s hs
  rw [ha s, ha ⟨poweredRadius D w s.val, hs⟩] at h
  exact h

theorem constantCoeff_norm_le (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w) :
    ‖a.coeff 0‖ ≤ ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a‖ := by
  have h := InitialThetaWittGeometricInterpolation.dividedTerm_le_realValue D w ρ
    (InitialThetaBoundedWittLocalization.inclusion D w a) 0
    (InitialThetaBoundedWittExpansion.wittInclusion D w a)
    (by simpa only [pow_zero, mul_one, InitialThetaBoundedWittExpansion.ambientInclusion,
      RingHom.comp_apply] using InitialThetaBoundedWittExpansion.toAmbient_inclusion D w a) 0
  rw [InitialThetaWittRhoExpansion.ainfMap, RingHom.comp_apply, InitialThetaWittRhoCompletion.inclusion_norm]
  simpa only [WittTeichmullerExpansion.digits, pow_zero, RingAut.one_apply,
    InitialThetaBoundedWittExpansion.wittInclusion_coeff_norm, mul_one, div_one] using h

end
end JoshiTeich.Act1Scene1.InitialThetaWittTeichmullerRecognition
