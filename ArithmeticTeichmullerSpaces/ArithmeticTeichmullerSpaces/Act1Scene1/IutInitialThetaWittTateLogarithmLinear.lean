import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedAdditiveHom
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithmBounded
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerTateBasis

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-LOGARITHM-LINEAR
source: Joshi II `eq:tate-module-of-lubin-tate`, `pr:teichmuller-lift-A/B`
and the rank-one Z_p Tate module inside the phi=p period space.
fidelity: proves integral scalar compatibility for the existing actual
Tate logarithm from its uniform radius bounds and p-power contraction.
The original topological Tate basis then proves continuity. Bundles the
same injective map as a continuous semilinear map over the canonical
inclusion Z_p -> Q_p, also with its actual phi=p subspace as codomain.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; paper B identity, full period comparisons and
period/BK identities remain open. No continuity or scalar law is assumed.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateLogarithmLinear

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittTateLogarithm
open InitialThetaWittAdditiveTatePeriod InitialThetaWittTateLogarithmInjective
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def scalarEvaluationHom (ρ : Radius) (t : Additive (Tate D w)) :
    PadicInt (Arithmetic.residueChar w.1) →+ InitialThetaWittRhoCompletion.Completed D w ρ :=
  (InitialThetaWittAllRadiusCompletion.evaluate D w ρ).toAddMonoidHom.comp
    ((tateLogHom D w).comp
      (LinearMap.toSpanSingleton (PadicInt (Arithmetic.residueChar w.1)) _ t).toAddMonoidHom)

theorem scalarEvaluationHom_apply (ρ : Radius) (t : Additive (Tate D w))
    (a : PadicInt (Arithmetic.residueChar w.1)) :
    scalarEvaluationHom D w ρ t a =
      InitialThetaWittAllRadiusCompletion.evaluate D w ρ (tateLogHom D w (a • t)) := rfl

theorem scalarEvaluationHom_continuous (ρ : Radius) (t : Additive (Tate D w)) :
    Continuous (scalarEvaluationHom D w ρ t) := by
  obtain ⟨C, _, hC⟩ := InitialThetaWittTateLogarithmBounded.exists_uniform_tateLog_bound D w ρ
  apply PadicBoundedAdditiveHom.continuous_of_bounded (Arithmetic.residueChar w.1)
    (scalarEvaluationHom D w ρ t) ρ.val.toReal ENNReal.toReal_nonneg ?_ ?_ C ?_
  · simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
        ρ.property.2
  · intro n x
    rw [nsmul_eq_mul, Nat.cast_pow, mul_comm]
    exact (InitialThetaWittScalarPrimeScaling.norm_mul_prime_pow D w ρ x n).le
  · intro a
    exact hC (a • t).toMul

theorem tateLogHom_padic_smul (a : PadicInt (Arithmetic.residueChar w.1))
    (t : Additive (Tate D w)) :
    tateLogHom D w (a • t) = (a : Padic (Arithmetic.residueChar w.1)) • tateLogHom D w t := by
  apply Subtype.ext
  funext ρ
  change InitialThetaWittAllRadiusCompletion.evaluate D w ρ (tateLogHom D w (a • t)) =
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ
      ((a : Padic (Arithmetic.residueChar w.1)) • tateLogHom D w t)
  rw [evaluate_smul]
  have h := PadicBoundedAdditiveHom.map_eq_smul_one (Arithmetic.residueChar w.1)
    (scalarEvaluationHom D w ρ t) (scalarEvaluationHom_continuous D w ρ t) a
  simpa only [scalarEvaluationHom_apply, one_smul] using h

def tateLogLinear : Additive (Tate D w) →ₛₗ[
    algebraMap (PadicInt (Arithmetic.residueChar w.1)) (Padic (Arithmetic.residueChar w.1))] Carrier D w where
  __ := tateLogHom D w
  map_smul' := tateLogHom_padic_smul D w

theorem tateLogHom_basis_formula (t : Additive (Tate D w)) :
    tateLogHom D w t =
      ((LocalKummer.TateBasis.equiv
        (p := Arithmetic.residueChar w.1)
        (Ω := InitialThetaCanonicalGeometricFontaine.coefficientField D w)).symm t :
        Padic (Arithmetic.residueChar w.1)) •
          tateLog D w (InitialThetaCyclotomicTateTilt.generator D w) := by
  let e := LocalKummer.TateBasis.equiv
    (p := Arithmetic.residueChar w.1)
    (Ω := InitialThetaCanonicalGeometricFontaine.coefficientField D w)
  have h := tateLogHom_padic_smul D w (e.symm t)
    (Additive.ofMul (InitialThetaCyclotomicTateTilt.generator D w))
  change tateLogHom D w (e (e.symm t)) = _ at h
  rw [e.apply_symm_apply] at h
  exact h

theorem tateLogHom_continuous : Continuous (tateLogHom D w) := by
  have he := (LocalKummer.TateBasis.equiv
    (p := Arithmetic.residueChar w.1)
    (Ω := InitialThetaCanonicalGeometricFontaine.coefficientField D w)).symm.continuous
  have h := (continuous_subtype_val.comp he).smul
    (continuous_const (y := tateLog D w (InitialThetaCyclotomicTateTilt.generator D w)))
  exact h.congr (fun t => (tateLogHom_basis_formula D w t).symm)

def tateLogContinuousLinear : Additive (Tate D w) →SL[
    algebraMap (PadicInt (Arithmetic.residueChar w.1)) (Padic (Arithmetic.residueChar w.1))] Carrier D w where
  __ := tateLogLinear D w
  cont := tateLogHom_continuous D w

def tateLogEigenContinuousLinear : Additive (Tate D w) →SL[
    algebraMap (PadicInt (Arithmetic.residueChar w.1)) (Padic (Arithmetic.residueChar w.1))]
      frobeniusPrimeSubmodule D w where
  __ := (tateLogLinear D w).codRestrict (frobeniusPrimeSubmodule D w)
    (fun t => tateLog_mem_frobeniusPrime D w t.toMul)
  cont := (tateLogHom_continuous D w).subtype_mk _

theorem tateLogEigenContinuousLinear_injective : Function.Injective (tateLogEigenContinuousLinear D w) :=
  tateLogEigenHom_injective D w

theorem tateLogEigenContinuousLinear_value (t : Tate D w) :
    (tateLogEigenContinuousLinear D w (Additive.ofMul t) : Carrier D w) = tateLog D w t := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateLogarithmLinear
