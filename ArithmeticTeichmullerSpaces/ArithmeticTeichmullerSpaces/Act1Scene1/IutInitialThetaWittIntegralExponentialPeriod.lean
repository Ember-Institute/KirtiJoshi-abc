import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTeichmullerRecognition
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalExponential
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalPrimeDivision

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-INTEGRAL-EXPONENTIAL-PERIOD
source: Joshi II `pr:teichmuller-lift-A` and
`eq:tate-module-of-lubin-tate`, multiplicative-formal-group periods.
fidelity: from an actual Ainf representative of the constructed annular
eigen exponential, rigidity gives its Teichmuller form. The original
zeroth-coefficient bound constructs a genuine principal tilt unit.
The proved local exp/log inverse identifies its actual period with the
full eigen element. Actual p-division removes a p-power scaling.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; integral representability is an explicit
source witness, not a global law or an assumed period identity. Its
existence for arbitrary annular exponentials remains open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittIntegralExponentialPeriod

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittEigenRadiusDynamics InitialThetaWittExponentialSeries
open InitialThetaWittExponentialContraction InitialThetaWittTeichmullerRecognition
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_small_annular_scaling (ρ : Radius) (z : Eigen D w) : ∃ k : ℕ,
    (∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val
        (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val‖ < s.val.val.toReal) ∧
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val ≤ ρ.val.toReal ^ 3 / 2 := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (radius_toReal_pos ρ).le
    (InitialThetaWittExponentialLinearization.radius_toReal_lt_one ρ)).mul_const
      (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val)
  rw [zero_mul] at h
  have hpos : 0 < min (ρ.val.toReal ^ (Arithmetic.residueChar w.1 + 1)) (ρ.val.toReal ^ 3 / 2) :=
    lt_min (pow_pos (radius_toReal_pos ρ) _) (div_pos (pow_pos (radius_toReal_pos ρ) _) (by norm_num))
  obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds hpos)).exists
  have hn : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val =
        ρ.val.toReal ^ k * InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val := by
    change InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z.val) = _
    rw [InitialThetaWittPadicScalarNorm.coordinateSeminorm_smul, map_pow, map_natCast, norm_pow,
      InitialThetaWittPadicScalarContinuity.norm_completed_prime]
  refine ⟨k, ?_, ?_⟩
  · intro s
    apply InitialThetaWittEigenAnnularSmallness.coordinate_lt_radius_of_le D w ρ _ _ s.val s.property
    rw [hn]
    exact (lt_min_iff.mp hk).1
  · rw [hn]
    exact (lt_min_iff.mp hk).2.le

theorem constantCoeff_near_one (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w)
    (ha : ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a - 1‖ ≤ smallRadius ρ) :
    ‖a.coeff 0 - 1‖ < 1 := by
  have h := constantCoeff_norm_le D w ρ (a - 1)
  change ‖WittVector.constantCoeff (a - 1)‖ ≤ _ at h
  rw [map_sub, map_one, map_sub, map_one] at h
  exact h.trans_lt (ha.trans_lt (smallRadius_lt_one ρ))

def principalOfLift (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w)
    (ha : ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a - 1‖ ≤ smallRadius ρ) : Principal D w := by
  let v : InitialThetaTiltField.Carrier D w := a.coeff 0
  have hv : ‖v - 1‖ < 1 := constantCoeff_near_one D w ρ a ha
  have hn : ‖v‖ = 1 := UltrametricPrincipalUnits.norm_eq_one (InitialThetaTiltField.Carrier D w) hv
  have hv0 : v ≠ 0 := norm_pos_iff.mp (hn ▸ zero_lt_one)
  exact ⟨Units.mk0 v hv0, hv⟩

theorem integralValue_principalOfLift (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w)
    (ha : ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a - 1‖ ≤ smallRadius ρ) :
    integralValue D w (principalOfLift D w ρ a ha) = a.coeff 0 := by
  apply Subtype.ext
  rfl

theorem wittUnit_principalOfLift (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w)
    (ha : ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a - 1‖ ≤ smallRadius ρ)
    (he : a = WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0)) :
    wittUnit D w (principalOfLift D w ρ a ha) = a := by
  change WittVector.teichmuller (Arithmetic.residueChar w.1)
    (integralValue D w (principalOfLift D w ρ a ha)) = a
  rw [integralValue_principalOfLift]
  exact he.symm

theorem exists_period_of_integral_annular_lift (ρ : Radius) (z : Eigen D w)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z.val‖ < s.val.val.toReal)
    (hsmall : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val ≤ ρ.val.toReal ^ 3 / 2)
    (a : InitialThetaTiltFontaine.Ainf D w)
    (ha : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ z.val hz) =
          InitialThetaWittRhoExpansion.ainfMap D w s.val a) :
    ∃ u : Principal D w, periodLog D w u = z.val := by
  have he := eq_teichmuller_of_annular_exponential_lift D w ρ z hz a ha
  have heval : exp D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ z.val) =
      InitialThetaWittRhoExpansion.ainfMap D w ρ a := ha ⟨ρ, le_rfl⟩
  have hb : ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a - 1‖ ≤ smallRadius ρ := by
    rw [← heval]
    apply (norm_exp_sub_one_le D w ρ _ (hz ⟨ρ, le_rfl⟩)).trans
    apply (div_le_iff₀ (radius_toReal_pos ρ)).mpr
    calc
      _ ≤ ρ.val.toReal ^ 3 / 2 := hsmall
      _ = _ := by unfold smallRadius; ring
  let u := principalOfLift D w ρ a hb
  have hu : wittUnit D w u = a := wittUnit_principalOfLift D w ρ a hb he
  refine ⟨u, InitialThetaWittPrincipalExponential.periodLog_eq_of_exp_teichmuller D w ρ z.val
    (hz ⟨ρ, le_rfl⟩) u ?_ ?_⟩
  · change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (coordinate D w u)‖ ≤ _
    change ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (wittUnit D w u - 1)‖ ≤ _
    rw [hu, map_sub, map_one]
    exact hb
  · rw [hu]
    exact heval

theorem exists_period_of_scaled_integral_annular_lift (ρ : Radius) (z : Eigen D w) (k : ℕ)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val
        (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val‖ < s.val.val.toReal)
    (hsmall : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val ≤ ρ.val.toReal ^ 3 / 2)
    (a : InitialThetaTiltFontaine.Ainf D w)
    (ha : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ
          (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val hz) =
            InitialThetaWittRhoExpansion.ainfMap D w s.val a) :
    ∃ u : Principal D w, periodLog D w u = z.val := by
  obtain ⟨u, hu⟩ := exists_period_of_integral_annular_lift D w ρ _ hz hsmall a ha
  refine ⟨InitialThetaWittPrincipalPrimeDivision.primeRoot D w k u, ?_⟩
  rw [InitialThetaWittPrincipalPrimeDivision.periodLog_primeRoot, hu]
  exact inv_smul_smul₀ (pow_ne_zero k
    (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)) z.val

end
end JoshiTeich.Act1Scene1.InitialThetaWittIntegralExponentialPeriod
