import ArithmeticTeichmullerSpaces.Act1Scene1.AdicResidueEvaluation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFontaineLocalization

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-COMPLETION
source: Joshi II canonical eta_K and primitive kernel (838, 932), and
B_cris subset B_st subset B_dR (1069--1076); Joshi III local Hodge rings
and the embedding into B_dR; Mathlib BDeRhamPlus and adic completion.
fidelity: uses Mathlib's original BDeRhamPlus of the same actual OΩ.
Extends the original Fontaine map to Ω, with exact principal maximal kernel,
completeness, locality and residue Ω. No residue/kernel certificate is input.
Does not assert DVR, period norms, a theta locus or a holomorphoid identity.
Original proofs, no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion

open JoshiTeich.Prologue
open InitialThetaFontaineLocalization
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

abbrev Source := Localization.Away (Arithmetic.residueChar w.1 :
  WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Source D w))

def sourceTheta : Source D w →+*
    InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  (untiltLocalizationEquiv D w).toRingHom.comp
    (fontaineThetaInvertP
      (LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
      (Arithmetic.residueChar w.1))

theorem sourceTheta_eq (a : Source D w) :
    sourceTheta D w a = InitialThetaFontaineLocalization.theta D w (sourceLocalizationEquiv D w a) :=
  (theta_sourceLocalization D w a).symm

theorem sourceTheta_surjective : Function.Surjective (sourceTheta D w) := by
  intro z
  obtain ⟨a, ha⟩ := InitialThetaFontaineLocalization.theta_surjective D w z
  refine ⟨(sourceLocalizationEquiv D w).symm a, ?_⟩
  rw [sourceTheta_eq, RingEquiv.apply_symm_apply, ha]

abbrev sourceKernel := RingHom.ker
  (fontaineThetaInvertP
    (LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (Arithmetic.residueChar w.1))

theorem sourceTheta_kernel : RingHom.ker (sourceTheta D w) = sourceKernel D w :=
  RingHom.ker_comp_of_injective _ (untiltLocalizationEquiv D w).injective

def sourcePrimitive : Source D w :=
  (sourceLocalizationEquiv D w).symm (localizedPrimitive D w)

theorem sourceKernel_eq_span : sourceKernel D w = Ideal.span {sourcePrimitive D w} := by
  ext a
  rw [← sourceTheta_kernel, RingHom.mem_ker, sourceTheta_eq,
    InitialThetaFontaineLocalization.mem_kernel_iff_dvd, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(sourceLocalizationEquiv D w).symm b, ?_⟩
    apply (sourceLocalizationEquiv D w).injective
    simpa only [map_mul, sourcePrimitive, RingEquiv.apply_symm_apply] using hb
  · rintro ⟨b, hb⟩
    refine ⟨sourceLocalizationEquiv D w b, ?_⟩
    rw [hb, map_mul, sourcePrimitive, RingEquiv.apply_symm_apply]

theorem sourceKernel_fg : (sourceKernel D w).FG := by
  rw [sourceKernel_eq_span]
  exact Submodule.fg_span_singleton _

def sourceQuotientEquiv : (Source D w ⧸ sourceKernel D w) ≃+*
    InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  (Ideal.quotEquivOfEq (sourceTheta_kernel D w).symm).trans
    ((sourceTheta D w).quotientKerEquivOfSurjective (sourceTheta_surjective D w))

theorem sourceQuotientEquiv_mk (a : Source D w) :
    sourceQuotientEquiv D w (Ideal.Quotient.mk _ a) = sourceTheta D w a := by
  unfold sourceQuotientEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk
    (f := sourceTheta D w) (sourceTheta_surjective D w) a

/-- The original Mathlib carrier, without a replacement completion. -/
abbrev Ring := BDeRhamPlus
  (LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
  (Arithmetic.residueChar w.1)

def theta : Ring D w →+* InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  AdicResidueEvaluation.evaluation (sourceKernel D w) (sourceQuotientEquiv D w)

theorem theta_of (a : Source D w) :
    theta D w (AdicCompletion.of (sourceKernel D w) (Source D w) a) = sourceTheta D w a :=
  sourceQuotientEquiv_mk D w a

theorem theta_of_actual (a : AinfInvertP D w) :
    theta D w (AdicCompletion.of (sourceKernel D w) (Source D w)
      ((sourceLocalizationEquiv D w).symm a)) = InitialThetaFontaineLocalization.theta D w a := by
  rw [theta_of, sourceTheta_eq, RingEquiv.apply_symm_apply]

theorem theta_surjective : Function.Surjective (theta D w) :=
  AdicResidueEvaluation.evaluation_surjective (sourceKernel D w) (sourceQuotientEquiv D w)

def primitive : Ring D w :=
  AdicCompletion.of (sourceKernel D w) (Source D w) (sourcePrimitive D w)

theorem theta_primitive : theta D w (primitive D w) = 0 := by
  rw [primitive, theta_of, sourceTheta_eq, sourcePrimitive, RingEquiv.apply_symm_apply]
  exact theta_localizedPrimitive D w

theorem kernel_eq_span : RingHom.ker (theta D w) = Ideal.span {primitive D w} :=
  AdicResidueEvaluation.kernel_eq_span (sourceKernel D w) (sourceQuotientEquiv D w)
    (sourcePrimitive D w) (sourceKernel_eq_span D w)

theorem kernel_isMaximal : (RingHom.ker (theta D w)).IsMaximal :=
  AdicResidueEvaluation.kernel_isMaximal (sourceKernel D w) (sourceQuotientEquiv D w)

instance complete : IsAdicComplete (RingHom.ker (theta D w)) (Ring D w) :=
  AdicResidueEvaluation.complete (sourceKernel D w) (sourceQuotientEquiv D w) (sourceKernel_fg D w)

instance localRing : IsLocalRing (Ring D w) :=
  AdicResidueEvaluation.localRing (sourceKernel D w) (sourceQuotientEquiv D w) (sourceKernel_fg D w)

local instance completedLocalRing :
    IsLocalRing (AdicCompletion (sourceKernel D w) (Source D w)) := localRing D w

theorem maximalIdeal_eq_kernel : IsLocalRing.maximalIdeal (Ring D w) = RingHom.ker (theta D w) :=
  AdicResidueEvaluation.maximalIdeal_eq_kernel (sourceKernel D w) (sourceQuotientEquiv D w)

theorem maximalIdeal_eq_span : IsLocalRing.maximalIdeal (Ring D w) = Ideal.span {primitive D w} :=
  (maximalIdeal_eq_kernel D w).trans (kernel_eq_span D w)

instance completeMaximalIdeal : IsAdicComplete (IsLocalRing.maximalIdeal (Ring D w)) (Ring D w) := by
  rw [maximalIdeal_eq_kernel]
  exact complete D w

theorem isUnit_iff (a : Ring D w) : IsUnit a ↔ theta D w a ≠ 0 :=
  AdicResidueEvaluation.isUnit_iff (sourceKernel D w) (sourceQuotientEquiv D w) a

def quotientEquiv : (Ring D w ⧸ RingHom.ker (theta D w)) ≃+*
    InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  AdicResidueEvaluation.quotientEquiv (sourceKernel D w) (sourceQuotientEquiv D w)

def residueEquiv : IsLocalRing.ResidueField (Ring D w) ≃+*
    InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq_kernel D w)).trans (quotientEquiv D w)

theorem residueEquiv_residue (a : Ring D w) :
    residueEquiv D w (IsLocalRing.residue (Ring D w) a) = theta D w a := by
  change quotientEquiv D w ((Ideal.quotEquivOfEq (maximalIdeal_eq_kernel D w))
    (Ideal.Quotient.mk _ a)) = theta D w a
  rw [Ideal.quotEquivOfEq_mk]
  exact AdicResidueEvaluation.quotientEquiv_mk
    (sourceKernel D w) (sourceQuotientEquiv D w) a

end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion
