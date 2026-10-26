import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitPeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogarithmLocalDetection

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-UNIT-INJECTIVE
source: Joshi II `pr:teichmuller-lift-A` and the identification of
principal tilt units with the actual phi=p period space.
fidelity: the actual normalized p-power quotient limit forces p-power
principal-unit coordinates to tend to zero. Local log detection then
turns a zero period into p-power torsion. Injectivity of the original
Witt maps and the actual perfect tilt Frobenius excludes that torsion.
Thus the existing principal-unit period homomorphism, also with its
actual phi=p codomain, is injective on the entire principal-unit group.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; surjectivity to the full phi=p space, its
evaluation and the full kernel comparison remain open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitInjective

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem integralValue_injective : Function.Injective (integralValue D w) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

theorem wittUnit_injective : Function.Injective (wittUnit D w) := by
  intro u v h
  apply integralValue_injective D w
  have hc := congrArg (fun a : InitialThetaTiltFontaine.Ainf D w => a.coeff 0) h
  simpa only [wittUnit, MonoidHom.comp_apply, WittVector.teichmuller_coeff_zero] using hc

theorem ainfCoordinate_eq_zero_iff (u : Principal D w) : ainfCoordinate D w u = 0 ↔ u = 1 := by
  rw [ainfCoordinate, sub_eq_zero, ← map_one (wittUnit D w), (wittUnit_injective D w).eq_iff]

theorem evaluate_coordinate_eq_zero_iff (ρ : Radius) (u : Principal D w) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (coordinate D w u) = 0 ↔ u = 1 := by
  change InitialThetaWittRhoCompletion.inclusion D w ρ
    (InitialThetaBoundedWittLocalization.inclusion D w (ainfCoordinate D w u)) = 0 ↔ u = 1
  rw [← map_zero (InitialThetaWittRhoCompletion.inclusion D w ρ),
    (InitialThetaWittRhoCompletion.inclusion_injective D w ρ).eq_iff,
    ← map_zero (InitialThetaBoundedWittLocalization.inclusion D w),
    (InitialThetaBoundedWittLocalization.inclusion_injective D w).eq_iff, ainfCoordinate_eq_zero_iff]

theorem prime_pow_smul_quotient (u : Principal D w) (k : ℕ) :
    ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) •
      InitialThetaWittIwasawaLimit.quotient D w (coordinate D w u) k =
        coordinate D w (u ^ (Arithmetic.residueChar w.1 ^ k)) := by
  have hp : (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k ≠ 0 :=
    pow_ne_zero k (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  rw [InitialThetaWittIwasawaLimit.quotient, smul_smul, mul_inv_cancel₀ hp, one_smul, coordinate_pow]

theorem tendsto_coordinate_prime_pow (u : Principal D w) :
    Filter.Tendsto (fun k : ℕ => coordinate D w (u ^ (Arithmetic.residueChar w.1 ^ k)))
      Filter.atTop (𝓝 0) := by
  have hp : Filter.Tendsto (fun k : ℕ =>
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := Arithmetic.residueChar w.1))
  have hq := InitialThetaWittIwasawaLimit.tendsto_quotient D w (coordinate D w u)
    (coordinate_lt_one D w u)
  simpa only [prime_pow_smul_quotient, zero_smul] using hp.smul hq

theorem prime_pow_eq_one_iff (u : Principal D w) (k : ℕ) :
    u ^ (Arithmetic.residueChar w.1 ^ k) = 1 ↔ u = 1 := by
  constructor
  · intro h
    apply integralValue_injective D w
    have he := congrArg (integralValue D w) h
    simp only [map_pow, map_one] at he ⊢
    apply (iterateFrobeniusEquiv (InitialThetaTiltIntegers.Integers D w)
      (Arithmetic.residueChar w.1) k).injective
    simpa only [iterateFrobeniusEquiv_def, one_pow] using he
  · rintro rfl
    exact one_pow _

theorem periodLog_eq_zero_iff (u : Principal D w) : periodLog D w u = 0 ↔ u = 1 := by
  constructor
  · intro hu
    let ρ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
    obtain ⟨δ, hδ, hdetect⟩ := InitialThetaWittLogarithmLocalDetection.exists_zero_detection D w ρ
    have hc := (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w _ _ _).mp
      (tendsto_coordinate_prime_pow D w u) ρ
    have hn : Filter.Tendsto (fun k : ℕ => ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ
        (coordinate D w (u ^ (Arithmetic.residueChar w.1 ^ k)))‖) Filter.atTop (𝓝 0) := by
      simpa only [map_zero, norm_zero] using hc.norm
    obtain ⟨k, hk⟩ := (hn.eventually (gt_mem_nhds hδ)).exists
    apply (prime_pow_eq_one_iff D w u k).mp
    apply (evaluate_coordinate_eq_zero_iff D w ρ _).mp
    apply hdetect _ (coordinate_lt_one D w _) hk.le
    change periodLog D w (u ^ (Arithmetic.residueChar w.1 ^ k)) = 0
    rw [periodLog_pow, hu, nsmul_zero]
  · rintro rfl
    exact periodLog_one D w

theorem periodLogHom_injective : Function.Injective (periodLogHom D w) := by
  apply (injective_iff_map_eq_zero (periodLogHom D w)).mpr
  intro u hu
  exact Additive.toMul.injective ((periodLog_eq_zero_iff D w u.toMul).mp hu)

theorem periodLog_injective : Function.Injective (periodLog D w) := by
  intro u v h
  exact Additive.ofMul.injective (periodLogHom_injective D w h)

theorem eigenLogHom_injective : Function.Injective (eigenLogHom D w) := by
  intro u v h
  exact periodLogHom_injective D w (congrArg Subtype.val h)

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitInjective
