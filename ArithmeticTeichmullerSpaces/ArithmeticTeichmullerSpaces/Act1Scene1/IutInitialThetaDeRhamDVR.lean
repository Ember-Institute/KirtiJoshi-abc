import ArithmeticTeichmullerSpaces.Act1Scene1.SeparatedPrincipalLocalRing
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-DVR
source: Joshi II primitive kernel and canonical eta_K (838, 932),
B_cris subset B_st subset B_dR (1069--1076); Joshi III local Hodge rings;
Mathlib BDeRhamPlus and the unit-times-uniformizer-power DVR criterion.
fidelity: the same actual BDeRhamPlus is a complete DVR; its actual primitive
is nonzero and a uniformizer. Every nonzero element is its power times a unit.
No domain, nonvanishing or DVR certificate is added to the actual inputs.
No period norms, theta locus or holomorphoid identity are asserted.
Original proofs, no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR

open JoshiTeich.Prologue InitialThetaDeRhamCompletion
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

local instance localizedDomain : IsDomain (InitialThetaFontaineLocalization.AinfInvertP D w) :=
  Localization.Away.isDomain (InitialThetaFontaineLocalization.prime_ne_zero D w)

local instance sourceDomain : IsDomain (Source D w) :=
  MulEquiv.isDomain (InitialThetaFontaineLocalization.AinfInvertP D w)
    (InitialThetaFontaineLocalization.sourceLocalizationEquiv D w).toMulEquiv

theorem sourcePrimitive_ne_zero : sourcePrimitive D w ≠ 0 := by
  intro h
  apply InitialThetaFontaineLocalization.localizedPrimitive_ne_zero D w
  have hh := congrArg (InitialThetaFontaineLocalization.sourceLocalizationEquiv D w) h
  simpa only [sourcePrimitive, RingEquiv.apply_symm_apply, map_zero] using hh

theorem sourcePrimitive_not_isUnit : ¬ IsUnit (sourcePrimitive D w) := by
  intro h
  have hz : sourceTheta D w (sourcePrimitive D w) = 0 := by
    rw [sourceTheta_eq, sourcePrimitive, RingEquiv.apply_symm_apply]
    exact InitialThetaFontaineLocalization.theta_localizedPrimitive D w
  have hu := h.map (sourceTheta D w)
  rw [hz] at hu
  exact not_isUnit_zero hu

theorem primitive_pow_ne_zero (n : ℕ) : primitive D w ^ n ≠ 0 :=
  SeparatedPrincipalLocalRing.completion_pow_ne_zero (sourceKernel D w) (sourcePrimitive D w)
    (sourceKernel_eq_span D w) (sourcePrimitive_ne_zero D w) (sourcePrimitive_not_isUnit D w) n

theorem primitive_ne_zero : primitive D w ≠ 0 := by
  simpa only [pow_one] using primitive_pow_ne_zero D w 1

theorem factorization (x : Ring D w) (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : (Ring D w)ˣ, x = primitive D w ^ n * u :=
  SeparatedPrincipalLocalRing.factorization (primitive D w) (maximalIdeal_eq_span D w) x hx

instance domain : IsDomain (Ring D w) :=
  SeparatedPrincipalLocalRing.domain (primitive D w) (maximalIdeal_eq_span D w)
    (primitive_pow_ne_zero D w)

instance discreteValuationRing : IsDiscreteValuationRing (Ring D w) :=
  SeparatedPrincipalLocalRing.discreteValuationRing (primitive D w) (maximalIdeal_eq_span D w)
    (primitive_pow_ne_zero D w)

theorem primitive_irreducible : Irreducible (primitive D w) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (primitive D w)
    (primitive_ne_zero D w) (maximalIdeal_eq_span D w)

theorem primitive_prime : Prime (primitive D w) :=
  (primitive_irreducible D w).prime

end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR
