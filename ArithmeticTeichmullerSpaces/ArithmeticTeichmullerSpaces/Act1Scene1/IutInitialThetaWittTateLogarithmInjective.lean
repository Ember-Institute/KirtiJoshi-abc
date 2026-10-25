import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogarithmLocalDetection
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAdditiveTatePeriod

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-LOGARITHM-INJECTIVE
source: Joshi II `eq:tate-module-of-lubin-tate`, `pr:teichmuller-lift-A/B`
and the inclusion of the actual Tate module in the phi=p periods.
fidelity: proves that actual p-power Tate coordinates tend to zero.
Local logarithm detection and injectivity of the original fixed-radius
Witt inclusion then force a zero-log tower to have p-power torsion.
Perfect tilt Frobenius excludes this torsion. The existing additive
Tate logarithm is therefore injective and its canonical period nonzero.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; Z_p linearity, full Tate-module comparison,
paper B identity and period/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateLogarithmInjective

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittTateLogarithm
open InitialThetaWittTateFrobeniusEigen InitialThetaWittAdditiveTatePeriod
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem prime_pow_smul_approximation (t : Tate D w) (k : ℕ) :
    ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) •
      approximation D w t k = coordinate D w (t ^ (Arithmetic.residueChar w.1 ^ k)) := by
  have hp : (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k ≠ 0 :=
    pow_ne_zero k (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  rw [approximation, smul_smul, mul_inv_cancel₀ hp, one_smul]

theorem tendsto_coordinate_prime_pow (t : Tate D w) :
    Filter.Tendsto (fun k : ℕ => coordinate D w (t ^ (Arithmetic.residueChar w.1 ^ k)))
      Filter.atTop (𝓝 0) := by
  have hp : Filter.Tendsto (fun k : ℕ =>
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := Arithmetic.residueChar w.1))
  simpa only [prime_pow_smul_approximation, zero_smul] using hp.smul (tendsto_approximation D w t)

theorem evaluate_coordinate_eq_zero_iff (ρ : Radius) (t : Tate D w) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (coordinate D w t) = 0 ↔ t = 1 := by
  change InitialThetaWittRhoCompletion.inclusion D w ρ
    (InitialThetaBoundedWittLocalization.tateCoordinate D w t) = 0 ↔ t = 1
  rw [← map_zero (InitialThetaWittRhoCompletion.inclusion D w ρ),
    (InitialThetaWittRhoCompletion.inclusion_injective D w ρ).eq_iff,
    InitialThetaBoundedWittLocalization.tateCoordinate_eq_zero_iff]

theorem prime_pow_eq_one_iff (t : Tate D w) (k : ℕ) :
    t ^ (Arithmetic.residueChar w.1 ^ k) = 1 ↔ t = 1 := by
  constructor
  · intro h
    apply InitialThetaCyclotomicTateTilt.epsilon_injective D w
    have he := congrArg (InitialThetaCyclotomicTateTilt.epsilon D w) h
    simp only [map_pow, map_one] at he ⊢
    apply (iterateFrobeniusEquiv (InitialThetaTiltIntegers.Integers D w)
      (Arithmetic.residueChar w.1) k).injective
    simpa only [iterateFrobeniusEquiv_def, one_pow] using he
  · rintro rfl
    exact one_pow _

theorem tateLog_eq_zero_iff (t : Tate D w) : tateLog D w t = 0 ↔ t = 1 := by
  constructor
  · intro ht
    let ρ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
    obtain ⟨δ, hδ, hdetect⟩ := InitialThetaWittLogarithmLocalDetection.exists_zero_detection D w ρ
    have hc := (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w _ _ _).mp
      (tendsto_coordinate_prime_pow D w t) ρ
    have hn : Filter.Tendsto (fun k : ℕ =>
        ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ
          (coordinate D w (t ^ (Arithmetic.residueChar w.1 ^ k)))‖)
        Filter.atTop (𝓝 0) := by
      simpa only [map_zero, norm_zero] using hc.norm
    obtain ⟨k, hk⟩ := (hn.eventually (gt_mem_nhds hδ)).exists
    apply (prime_pow_eq_one_iff D w t k).mp
    apply (evaluate_coordinate_eq_zero_iff D w ρ _).mp
    apply hdetect _ (coordinate_lt_one D w _) hk.le
    change tateLog D w (t ^ (Arithmetic.residueChar w.1 ^ k)) = 0
    rw [tateLog_pow, ht, nsmul_zero]
  · rintro rfl
    exact tateLog_one D w

theorem tateLogHom_injective : Function.Injective (tateLogHom D w) := by
  apply (injective_iff_map_eq_zero (tateLogHom D w)).mpr
  intro t ht
  exact Additive.toMul.injective ((tateLog_eq_zero_iff D w t.toMul).mp ht)

theorem tateLog_injective : Function.Injective (tateLog D w) := by
  intro x y h
  exact Additive.ofMul.injective (tateLogHom_injective D w h)

theorem tateLogEigenHom_injective : Function.Injective (tateLogEigenHom D w) := by
  intro x y h
  apply tateLogHom_injective D w
  exact congrArg Subtype.val h

theorem canonical_tateLog_ne_zero :
    tateLog D w (InitialThetaCyclotomicTateTilt.generator D w) ≠ 0 := by
  intro h
  exact InitialThetaCyclotomicTateTilt.generator_ne_one D w
    ((tateLog_eq_zero_iff D w _).mp h)

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateLogarithmInjective
