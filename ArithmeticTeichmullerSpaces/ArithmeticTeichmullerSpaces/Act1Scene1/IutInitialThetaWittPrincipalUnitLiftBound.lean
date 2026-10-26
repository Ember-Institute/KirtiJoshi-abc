import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFontaineKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-UNIT-LIFT-BOUND
source: Joshi II `pr:teichmuller-lift-A` and the multiplicative formal
group description of B^{phi=p} following that proposition.
fidelity: the actual Witt mod-p decomposition bounds the constant
coefficient by max(norm(theta(a)), norm(p)). Applied to [integralLift(z)]-1,
this proves that the actual compatible-root lift of any untilt principal
unit is a tilt principal unit. No additivity of sharp is assumed.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the actual principal-group and period consumers
are separate. No new input law or period-surjectivity assumption. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitLiftBound

open JoshiTeich.Prologue InitialThetaWittThetaBound
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem constantCoeff_norm_le_max (a : Ainf D w) :
    ‖a.coeff 0‖ ≤ max ‖integralEvaluation D w a‖
      ‖(Arithmetic.residueChar w.1 : Untilt D w)‖ := by
  obtain ⟨b, hb⟩ := InitialThetaFontaineKernel.decomposition D w a
  have he : integralEvaluation D w (WittVector.teichmuller
      (Arithmetic.residueChar w.1) (a.coeff 0)) =
      integralEvaluation D w a - (Arithmetic.residueChar w.1 : Untilt D w) *
        integralEvaluation D w b := by
    have h := congrArg (integralEvaluation D w) hb
    rw [map_add, map_mul, map_natCast] at h
    exact eq_sub_of_add_eq h.symm
  calc
    ‖a.coeff 0‖ = ‖integralEvaluation D w (WittVector.teichmuller
      (Arithmetic.residueChar w.1) (a.coeff 0))‖ :=
        (integralEvaluation_teichmuller_norm D w _).symm
    _ = ‖integralEvaluation D w a - (Arithmetic.residueChar w.1 : Untilt D w) *
        integralEvaluation D w b‖ := congrArg norm he
    _ ≤ max ‖integralEvaluation D w a‖
        ‖(Arithmetic.residueChar w.1 : Untilt D w) * integralEvaluation D w b‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        IsUltrametricDist.norm_add_le_max (integralEvaluation D w a)
          (-((Arithmetic.residueChar w.1 : Untilt D w) * integralEvaluation D w b))
    _ ≤ _ := max_le_max_left _ (by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (integralEvaluation_norm_le_one D w b))

theorem constantCoeff_norm_lt_one (a : Ainf D w)
    (ha : ‖integralEvaluation D w a‖ < 1) : ‖a.coeff 0‖ < 1 :=
  (constantCoeff_norm_le_max D w a).trans_lt
    (max_lt ha (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2)

theorem integralLift_near_one
    (z : LocalGeometricFontaine.integerRing (Untilt D w))
    (hz : ‖(z : Untilt D w) - 1‖ < 1) :
    ‖(InitialThetaTiltFontaine.integralLift D w z : InitialThetaTiltField.Carrier D w) - 1‖ < 1 := by
  let a : Ainf D w := WittVector.teichmuller (Arithmetic.residueChar w.1)
    (InitialThetaTiltFontaine.integralLift D w z) - 1
  have he : integralEvaluation D w a = (z : Untilt D w) - 1 := by
    change integralEvaluation D w (WittVector.teichmuller (Arithmetic.residueChar w.1)
      (InitialThetaTiltFontaine.integralLift D w z) - 1) = _
    rw [map_sub, map_one]
    exact congrArg (fun q : LocalGeometricFontaine.integerRing (Untilt D w) =>
      (q : Untilt D w) - 1) (InitialThetaTiltFontaine.theta_integralLift D w z)
  have ha := constantCoeff_norm_lt_one D w a (he ▸ hz)
  have hc : a.coeff 0 = InitialThetaTiltFontaine.integralLift D w z - 1 := by
    change WittVector.constantCoeff (WittVector.teichmuller (Arithmetic.residueChar w.1)
      (InitialThetaTiltFontaine.integralLift D w z) - 1) = _
    rw [map_sub, map_one]
    change (WittVector.teichmuller (Arithmetic.residueChar w.1)
      (InitialThetaTiltFontaine.integralLift D w z)).coeff 0 - 1 = _
    rw [WittVector.teichmuller_coeff_zero]
  rw [hc] at ha
  exact ha

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitLiftBound
