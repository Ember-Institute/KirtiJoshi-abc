import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittCompletedIntegralCriterion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittBoundedFrobeniusIntegral

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-COMPLETED-FROBENIUS-RECOGNITION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, recognition
of multiplicative Frobenius solutions in the completed period ring.
fidelity: on the entire original common completion, phi(x)=x^p forces
all original rho norms to be equal. A unit bound at one radius constructs
an original integral Teichmuller representative. A contracting original
Teichmuller factor removes that unit-bound restriction and constructs
an actual bounded source representative for every such solution.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this concerns full common-ring solutions.
No extension of annular solutions to the common ring is assumed or
asserted. Annular exponential lifts and full Tate-kernel classification
remain open. Original carriers, norms and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittCompletedFrobeniusRecognition

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius InitialThetaWittRhoFrobeniusCompletion
open InitialThetaWittEigenRadiusDynamics
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius
abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w

theorem coordinate_powered (ρ : Radius) (x : Carrier D w)
    (hx : frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1) :
    coordinateSeminorm D w (poweredRadius D w ρ) x = coordinateSeminorm D w ρ x := by
  have h := coordinateSeminorm_frobenius D w ρ x
  rw [hx] at h
  change ‖evaluate D w (poweredRadius D w ρ) (x ^ Arithmetic.residueChar w.1)‖ = _ at h
  rw [map_pow, norm_pow] at h
  exact (pow_left_inj₀ (apply_nonneg _ _) (apply_nonneg _ _)
    (Arithmetic.residueChar_prime w.1).ne_zero).mp h

theorem coordinate_radiusOrbit (ρ : Radius) (x : Carrier D w)
    (hx : frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1) (n : ℕ) :
    coordinateSeminorm D w (radiusOrbit D w ρ n) x = coordinateSeminorm D w ρ x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [radiusOrbit, coordinate_powered D w _ x hx, ih]

theorem coordinate_eq (ρ r : Radius) (x : Carrier D w)
    (hx : frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1) :
    coordinateSeminorm D w r x = coordinateSeminorm D w ρ x := by
  have hle (a b : Radius) : coordinateSeminorm D w b x ≤ coordinateSeminorm D w a x := by
    obtain ⟨n, hn⟩ := exists_radiusOrbit_le D w b a
    obtain ⟨m, hm⟩ := exists_radiusOrbit_le D w a (radiusOrbit D w b n)
    have h := InitialThetaWittRadiusInterpolation.coordinateSeminorm_le_endpoint_max D w
      (radiusOrbit D w a m) (radiusOrbit D w b n) a hm hn x
    simpa only [coordinate_radiusOrbit D w _ x hx, max_self] using h
  exact le_antisymm (hle ρ r) (hle r ρ)

theorem exists_integral_teichmuller (ρ : Radius) (x : Carrier D w)
    (hx : frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1)
    (hn : coordinateSeminorm D w ρ x ≤ 1) :
    ∃ a : InitialThetaTiltIntegers.Integers D w,
      InitialThetaWittAllRadiusExpansion.ainfMap D w
        (WittVector.teichmuller (Arithmetic.residueChar w.1) a) = x := by
  obtain ⟨a, ha⟩ := InitialThetaWittCompletedIntegralCriterion.exists_integral_of_unit_bounds D w ρ x
    (fun r => by change coordinateSeminorm D w r x ≤ 1; rw [coordinate_eq D w ρ r x hx]; exact hn)
  have he : InitialThetaWittRhoFrobeniusEquiv.completedEquiv D w ρ
      (InitialThetaWittRhoExpansion.ainfMap D w ρ a) =
        InitialThetaWittRhoExpansion.ainfMap D w (poweredRadius D w ρ) a ^ Arithmetic.residueChar w.1 := by
    have h := evaluate_frobenius D w ρ x
    rw [hx, ← ha, map_pow] at h
    exact h.symm
  have ht := InitialThetaWittTeichmullerRecognition.eq_teichmuller_of_completed_equation D w ρ a he
  exact ⟨a.coeff 0, (congrArg (InitialThetaWittAllRadiusExpansion.ainfMap D w) ht).symm.trans ha⟩

theorem exists_bounded_source (ρ : Radius) (x : Carrier D w)
    (hx : frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1) :
    ∃ a : InitialThetaBoundedWittLocalization.Ring D w, inclusion D w a = x := by
  let v := InitialThetaBoundedWittLocalization.varpi D w
  have hv := InitialThetaBoundedWittLocalization.varpi_norm_pos_lt_one D w
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hv.1.le hv.2).mul_const
    (coordinateSeminorm D w ρ x)
  rw [zero_mul] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  let a : InitialThetaTiltFontaine.Ainf D w := InitialThetaBoundedWittLocalization.teichVarpi D w ^ n
  let q : Carrier D w := InitialThetaWittAllRadiusExpansion.ainfMap D w a
  have hq : frobeniusEquiv D w q = q ^ Arithmetic.residueChar w.1 := by
    change frobeniusEquiv D w (inclusion D w (InitialThetaBoundedWittLocalization.inclusion D w
      (InitialThetaBoundedWittLocalization.teichVarpi D w ^ n))) = _
    rw [frobenius_inclusion]
    change inclusion D w (InitialThetaBoundedWittLocalization.frobenius D w
      (InitialThetaBoundedWittLocalization.inclusion D w
        (InitialThetaBoundedWittLocalization.teichVarpi D w ^ n))) = _
    rw [InitialThetaBoundedWittLocalization.frobenius_inclusion]
    rw [map_pow, InitialThetaBoundedWittLocalization.sourceFrobenius_teichVarpi]
    change inclusion D w (InitialThetaBoundedWittLocalization.inclusion D w
      ((InitialThetaBoundedWittLocalization.teichVarpi D w ^ Arithmetic.residueChar w.1) ^ n)) =
      (inclusion D w (InitialThetaBoundedWittLocalization.inclusion D w
        (InitialThetaBoundedWittLocalization.teichVarpi D w ^ n))) ^ Arithmetic.residueChar w.1
    simp only [map_pow]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hqx : frobeniusEquiv D w (q * x) = (q * x) ^ Arithmetic.residueChar w.1 := by
    rw [map_mul, hq, hx, mul_pow]
  have hqn : coordinateSeminorm D w ρ q = ‖v‖ ^ n := by
    change ‖InitialThetaWittRhoExpansion.ainfMap D w ρ
      (InitialThetaBoundedWittLocalization.teichVarpi D w ^ n)‖ = _
    rw [map_pow, norm_pow]
    congr 1
    exact InitialThetaWittTateLogarithm.norm_ainf_teichmuller D w ρ v
  have hsmall : coordinateSeminorm D w ρ (q * x) ≤ 1 := by
    rw [InitialThetaWittMultiplicativeNorm.coordinateSeminorm_mul, hqn]
    exact hn.le
  obtain ⟨b, hb⟩ := exists_integral_teichmuller D w ρ (q * x) hqx hsmall
  obtain ⟨u, hu⟩ := (InitialThetaBoundedWittLocalization.teichVarpi_isUnit D w).pow n
  let z := InitialThetaBoundedWittLocalization.inclusion D w
    (WittVector.teichmuller (Arithmetic.residueChar w.1) b)
  refine ⟨((u⁻¹ : (InitialThetaBoundedWittLocalization.Ring D w)ˣ) :
    InitialThetaBoundedWittLocalization.Ring D w) * z, ?_⟩
  have hqu : inclusion D w (u : InitialThetaBoundedWittLocalization.Ring D w) = q := by
    rw [hu, ← map_pow]
    rfl
  change inclusion D w (((u⁻¹ : (InitialThetaBoundedWittLocalization.Ring D w)ˣ) :
    InitialThetaBoundedWittLocalization.Ring D w) * z) = x
  rw [map_mul]
  have hz : inclusion D w z = q * x := hb
  rw [hz, ← hqu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

end
end JoshiTeich.Act1Scene1.InitialThetaWittCompletedFrobeniusRecognition
