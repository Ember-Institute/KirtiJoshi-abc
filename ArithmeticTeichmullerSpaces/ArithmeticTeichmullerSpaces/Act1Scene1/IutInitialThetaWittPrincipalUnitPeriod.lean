import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitDomain
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAdditiveTatePeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithmInjective
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaPadicCompatibility

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-UNIT-PERIOD
source: Joshi II `pr:teichmuller-lift-A` and the description of
B^{phi=p} using the multiplicative formal group 1+m_F.
fidelity: the actual log([u]) series converges at all radii for every
principal tilt unit. Its proved logarithmic product law makes it an
additive period map. Actual Witt Frobenius and the group power law
prove phi=p. Continuous canonical evaluation sends this same period
to the convergent logarithm series of sharp(u) in the original untilt.
The original Tate epsilon elements are actual principal units, and this
map agrees with their original nonzero Tate logarithm.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the full principal-unit/period isomorphism,
surjectivity to the untilt and the full kernel comparison remain open.
No universal-cover or logarithm comparison law is input. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitPeriod

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittPrincipalUnitDomain InitialThetaWittLogarithmSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def periodLog (u : Principal D w) : Carrier D w := logOneAdd D w (coordinate D w u)

theorem hasSum_periodLog (u : Principal D w) :
    HasSum (logTerm D w (coordinate D w u)) (periodLog D w u) :=
  hasSum_logOneAdd D w _ (coordinate_lt_one D w u)

theorem periodLog_one : periodLog D w 1 = 0 := by
  rw [periodLog, coordinate_one, logOneAdd_zero]

theorem periodLog_mul (u v : Principal D w) :
    periodLog D w (u * v) = periodLog D w u + periodLog D w v := by
  unfold periodLog
  rw [coordinate_mul]
  exact InitialThetaWittLogarithmMultiplication.logOneAdd_mul_coordinate D w _ _
    (coordinate_lt_one D w u) (coordinate_lt_one D w v)

def periodLogHom : Additive (Principal D w) →+ Carrier D w where
  toFun u := periodLog D w u.toMul
  map_zero' := periodLog_one D w
  map_add' u v := periodLog_mul D w u.toMul v.toMul

theorem periodLog_pow (u : Principal D w) (n : ℕ) :
    periodLog D w (u ^ n) = n • periodLog D w u := by
  have h := (periodLogHom D w).map_nsmul n (Additive.ofMul u)
  change periodLog D w ((n • Additive.ofMul u).toMul) = n • periodLog D w u at h
  simpa only [toMul_nsmul, toMul_ofMul] using h

theorem frobenius_coordinate (u : Principal D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (coordinate D w u) =
      coordinate D w (u ^ Arithmetic.residueChar w.1) := by
  have he : InitialThetaBoundedWittLocalization.sourceFrobenius D w (ainfCoordinate D w u) =
      ainfCoordinate D w (u ^ Arithmetic.residueChar w.1) := by
    change InitialThetaTateFrobenius.phi D w (wittUnit D w u - 1) =
      wittUnit D w (u ^ Arithmetic.residueChar w.1) - 1
    simp only [wittUnit, MonoidHom.comp_apply, map_sub, map_one,
      InitialThetaTateFrobenius.phi_teichmuller, map_pow]
  change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
    (InitialThetaWittAllRadiusCompletion.inclusion D w
      (InitialThetaBoundedWittLocalization.inclusion D w (ainfCoordinate D w u))) = _
  rw [InitialThetaWittAllRadiusFrobenius.frobenius_inclusion]
  change InitialThetaWittAllRadiusCompletion.inclusion D w
    (InitialThetaBoundedWittLocalization.frobenius D w
      (InitialThetaBoundedWittLocalization.inclusion D w (ainfCoordinate D w u))) = _
  rw [InitialThetaBoundedWittLocalization.frobenius_inclusion]
  exact congrArg (InitialThetaWittAllRadiusExpansion.ainfMap D w) he

theorem frobenius_periodLog (u : Principal D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (periodLog D w u) =
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • periodLog D w u := by
  change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (logOneAdd D w (coordinate D w u)) = _
  rw [frobenius_logOneAdd D w _ (coordinate_lt_one D w u), frobenius_coordinate]
  change periodLog D w (u ^ Arithmetic.residueChar w.1) = _
  rw [periodLog_pow, Nat.cast_smul_eq_nsmul]

def eigenLogHom : Additive (Principal D w) →+ InitialThetaWittAdditiveTatePeriod.frobeniusPrimeSubmodule D w where
  toFun u := ⟨periodLog D w u.toMul, frobenius_periodLog D w u.toMul⟩
  map_zero' := Subtype.ext (periodLog_one D w)
  map_add' u v := Subtype.ext (periodLog_mul D w u.toMul v.toMul)

def untiltCoordinate (u : Principal D w) : InitialThetaWittThetaBound.Untilt D w :=
  (InitialThetaTiltIntegers.sharp D w (integralValue D w u) : InitialThetaWittThetaBound.Untilt D w) - 1

theorem evaluation_coordinate (u : Principal D w) :
    InitialThetaWittThetaEvaluation.evaluation D w (coordinate D w u) = untiltCoordinate D w u := by
  rw [coordinate, InitialThetaWittThetaEvaluation.evaluation_ainfMap, ainfCoordinate, map_sub, map_one]
  exact congrArg (fun z : LocalGeometricFontaine.integerRing (InitialThetaWittThetaBound.Untilt D w) =>
    (z : InitialThetaWittThetaBound.Untilt D w) - 1)
      (InitialThetaTiltFontaine.theta_teichmuller D w (integralValue D w u))

theorem untiltCoordinate_lt_one (u : Principal D w) : ‖untiltCoordinate D w u‖ < 1 := by
  rw [← evaluation_coordinate]
  exact (InitialThetaWittThetaEvaluation.evaluation_norm_le D w _).trans_lt
    (coordinate_lt_one D w u (InitialThetaWittThetaBound.radius D w))

theorem evaluation_logTerm (u : Principal D w) (n : ℕ) :
    InitialThetaWittThetaEvaluation.evaluation D w (logTerm D w (coordinate D w u) n) =
      logCoefficient D w n • untiltCoordinate D w u ^ n := by
  rw [logTerm, InitialThetaWittThetaPadicCompatibility.evaluation_smul, map_pow, evaluation_coordinate]

theorem hasSum_evaluation_periodLog (u : Principal D w) :
    HasSum (fun n : ℕ => logCoefficient D w n • untiltCoordinate D w u ^ n)
      (InitialThetaWittThetaEvaluation.evaluation D w (periodLog D w u)) := by
  have h : HasSum (fun n : ℕ => InitialThetaWittThetaEvaluation.evaluation D w
      (logTerm D w (coordinate D w u) n))
      (InitialThetaWittThetaEvaluation.evaluation D w (periodLog D w u)) :=
    (hasSum_periodLog D w u).map (InitialThetaWittThetaEvaluation.evaluation D w)
      (InitialThetaWittThetaEvaluation.evaluation_continuous D w)
  simpa only [evaluation_logTerm] using h

theorem evaluation_periodLog_eq_tsum (u : Principal D w) :
    InitialThetaWittThetaEvaluation.evaluation D w (periodLog D w u) =
      ∑' n : ℕ, logCoefficient D w n • untiltCoordinate D w u ^ n :=
  (hasSum_evaluation_periodLog D w u).tsum_eq.symm

theorem tate_epsilon_near_one (t : InitialThetaWittTateLogarithm.Tate D w) :
    ‖(InitialThetaCyclotomicTateTilt.epsilon D w t : InitialThetaTiltField.Carrier D w) - 1‖ < 1 := by
  have h := (InitialThetaFontaineKernel.constantCoeff_norm_le D w
    (InitialThetaCyclotomicTateTilt.kernelCoordinate D w t)
    (InitialThetaCyclotomicTateTilt.kernelCoordinate_mem_ker D w t)).trans_lt
      (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2
  have hc : (InitialThetaCyclotomicTateTilt.kernelCoordinate D w t).coeff 0 =
      InitialThetaCyclotomicTateTilt.epsilon D w t - 1 := by
    change WittVector.constantCoeff (InitialThetaCyclotomicTateTilt.teichmuller D w t - 1) = _
    rw [map_sub, map_one]
    change (WittVector.teichmuller (Arithmetic.residueChar w.1)
      (InitialThetaCyclotomicTateTilt.epsilon D w t)).coeff 0 - 1 = _
    rw [WittVector.teichmuller_coeff_zero]
  rw [hc] at h
  have hn : ‖InitialThetaCyclotomicTateTilt.epsilon D w t - 1‖ =
      ‖(InitialThetaCyclotomicTateTilt.epsilon D w t : InitialThetaTiltField.Carrier D w) - 1‖ := rfl
  exact hn ▸ h

def tatePrincipal (t : InitialThetaWittTateLogarithm.Tate D w) : Principal D w := by
  let v : InitialThetaTiltField.Carrier D w := InitialThetaCyclotomicTateTilt.epsilon D w t
  have hv : ‖v‖ = 1 := UltrametricPrincipalUnits.norm_eq_one _ (tate_epsilon_near_one D w t)
  have hv0 : v ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hv]
    exact zero_lt_one
  exact ⟨Units.mk0 v hv0, tate_epsilon_near_one D w t⟩

theorem integralValue_tatePrincipal (t : InitialThetaWittTateLogarithm.Tate D w) :
    integralValue D w (tatePrincipal D w t) = InitialThetaCyclotomicTateTilt.epsilon D w t := by
  apply Subtype.ext
  rfl

theorem periodLog_tatePrincipal (t : InitialThetaWittTateLogarithm.Tate D w) :
    periodLog D w (tatePrincipal D w t) = InitialThetaWittTateLogarithm.tateLog D w t := by
  change logOneAdd D w (InitialThetaWittAllRadiusExpansion.ainfMap D w
      (WittVector.teichmuller (Arithmetic.residueChar w.1) (integralValue D w (tatePrincipal D w t)) - 1)) =
    logOneAdd D w (InitialThetaWittAllRadiusExpansion.ainfMap D w
      (WittVector.teichmuller (Arithmetic.residueChar w.1) (InitialThetaCyclotomicTateTilt.epsilon D w t) - 1))
  rw [integralValue_tatePrincipal]

theorem canonical_periodLog_ne_zero :
    periodLog D w (tatePrincipal D w (InitialThetaCyclotomicTateTilt.generator D w)) ≠ 0 := by
  rw [periodLog_tatePrincipal]
  exact InitialThetaWittTateLogarithmInjective.canonical_tateLog_ne_zero D w

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitPeriod
