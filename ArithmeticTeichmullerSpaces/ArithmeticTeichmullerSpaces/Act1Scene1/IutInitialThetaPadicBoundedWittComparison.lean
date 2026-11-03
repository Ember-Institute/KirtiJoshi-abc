import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicTiltWittComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLocalizationChoice
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.WittMappedLocalizationComparisonData
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittExpansion
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-BOUNDED-WITT-COMPARISON
source: Joshi II `se:ff-rings`, W(O_F)[1/p,1/[t]], and the proved
actual-to-standard tilt integer-ring comparison.
fidelity: compares the existing actual bounded Witt localization with the
independent standard C_p tilt localization. Pulls the independently chosen
standard contraction back through the integer-ring equivalence, proves it
is nonzero and contracting using the original local-degree norm law, and
uses the proved independence of the actual contracting element. The
inclusion formula retains the same Witt coefficient map.
boundary: this is an algebraic localization comparison. The rho completion
and identification with the paper's completed B remain open. Original proofs;
Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
open scoped ENNReal
noncomputable section

private theorem inverse_ne_zero {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (s : S) (hs : s ≠ 0) : e.symm s ≠ 0 := by
  intro h
  apply hs
  calc
    s = e (e.symm s) := (e.apply_symm_apply s).symm
    _ = 0 := by rw [h, map_zero]

private theorem inverse_norm_lt_one {R S : Type*} [CommRing R] [CommRing S]
    [Norm R] [Norm S] (e : R ≃+* S) (d : ℕ) (hd : 0 < d)
    (hn : ∀ x, ‖e x‖ ^ d = ‖x‖) (s : S)
    (hs0 : 0 ≤ ‖s‖) (hs1 : ‖s‖ < 1) : ‖e.symm s‖ < 1 := by
  rw [← hn (e.symm s), e.apply_symm_apply]
  exact pow_lt_one₀ hs0 hs1 hd.ne'

private theorem inverse_norm_power {R S : Type*} [CommRing R] [CommRing S]
    [Norm R] [Norm S] (e : R ≃+* S) (d : ℕ)
    (hn : ∀ x, ‖e x‖ ^ d = ‖x‖) (s : S) :
    ‖s‖ ^ d = ‖e.symm s‖ := by
  simpa only [e.apply_symm_apply] using hn (e.symm s)

private theorem inverse_radius_power {R S : Type*} [CommRing R] [CommRing S]
    [Norm R] [Norm S] (e : R ≃+* S) (d : ℕ)
    (hn : ∀ x, ‖e x‖ ^ d = ‖x‖) (s : S) (hs : 0 ≤ ‖s‖)
    (ρ : ℝ≥0∞) :
    (ρ * ENNReal.ofReal ‖s‖) ^ d =
      ρ ^ d * ENNReal.ofReal ‖e.symm s‖ := by
  rw [mul_pow, ← ENNReal.ofReal_pow hs d, inverse_norm_power e d hn s]

universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

-- Cache the original equivalence with the independent model's integer-ring interface.
def integerEquiv : InitialThetaTiltIntegers.Integers D w ≃+*
    PadicTiltField.Integers (Arithmetic.residueChar w.1) :=
  InitialThetaPadicTiltTopology.integerEquiv D w

/-- The independent standard contraction transported to the actual tilt integers. -/
def contraction :=
  (integerEquiv D w).symm
    (PadicBoundedWittLocalization.contraction (Arithmetic.residueChar w.1))

theorem contraction_ne_zero : contraction D w ≠ 0 :=
  inverse_ne_zero (integerEquiv D w)
    (PadicBoundedWittLocalization.contraction (Arithmetic.residueChar w.1))
    (PadicBoundedWittLocalization.contraction_ne_zero (Arithmetic.residueChar w.1))

section InferredProofs
-- Retain the coefficient-ring norm instances of the original comparison.
set_option linter.defProp false

private def integerNormPower (x : InitialThetaTiltIntegers.Integers D w) :
    ‖integerEquiv D w x‖ ^ Arithmetic.localDeg w.1 = ‖x‖ :=
  InitialThetaPadicTiltTopology.integerEquiv_norm_pow D w x

private def contractionNormTransfer := inverse_norm_lt_one (integerEquiv D w)

def contraction_norm_lt_one :=
  contractionNormTransfer D w
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (integerNormPower D w)
    (PadicBoundedWittLocalization.contraction (Arithmetic.residueChar w.1))
    (norm_nonneg _)
    (PadicBoundedWittLocalization.contraction_norm_lt_one (Arithmetic.residueChar w.1))

private def contractionRadiusTransfer := inverse_radius_power (integerEquiv D w)

def contraction_radius_pow :=
  contractionRadiusTransfer D w (Arithmetic.localDeg w.1) (integerNormPower D w)
    (PadicBoundedWittLocalization.contraction (Arithmetic.residueChar w.1))
    (norm_nonneg _)

end InferredProofs

/-- Change the contraction while fixing the original actual Ainf. -/
def choiceEquiv :=
  InitialThetaWittLocalizationChoice.choiceEquiv D w (contraction D w)
    (contraction_ne_zero D w) (contraction_norm_lt_one D w)

def integerWittEquiv := WittRingEquiv.mapEquiv (Arithmetic.residueChar w.1)
  (integerEquiv D w)

/-- The integral Witt map with its original input and output carriers fixed. -/
def integerWittFun (a : InitialThetaTiltFontaine.Ainf D w) :
    PadicBoundedWittLocalization.Ainf (Arithmetic.residueChar w.1) :=
  (integerWittEquiv D w).toEquiv.toFun a

private def choiceObserverTransfer :=
  WittMappedLocalizationComparisonData.ofNormEquivWithObservers (Arithmetic.residueChar w.1)
    (fun a n => ‖(InitialThetaBoundedWittExpansion.wittInclusion D w a).coeff n‖)
    (fun a n => ‖(PadicBoundedWittExpansion.wittInclusion (Arithmetic.residueChar w.1) a).coeff n‖)
    (InitialThetaBoundedWittExpansion.wittInclusion_coeff_norm D w)
    (PadicBoundedWittExpansion.wittInclusion_coeff_norm (Arithmetic.residueChar w.1))

private def choiceNormTransfer := choiceObserverTransfer D w (integerEquiv D w)

/-- Construct the maps and their coefficient norm laws in one carrier. -/
def choicePresentationData :=
  choiceNormTransfer D w (contraction D w)
    (PadicBoundedWittLocalization.contraction (Arithmetic.residueChar w.1))
    ((integerEquiv D w).apply_symm_apply _)
    (Arithmetic.localDeg w.1) (integerNormPower D w)


/-- Transport the localization using the map saved with its presentation laws. -/
def choiceStandardEquiv := (choicePresentationData D w).locEquiv

/-- Expose the localization map on the two original bounded carriers. -/
def choiceStandardFun
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w (contraction D w)) :
    PadicBoundedWittLocalization.Ring (Arithmetic.residueChar w.1) :=
  choiceStandardEquiv D w x

set_option linter.defProp false in
def choiceStandardEquiv_presentation := (choicePresentationData D w).on_presentation

theorem choiceStandardEquiv_algebraMap
    (x : InitialThetaTiltFontaine.Ainf D w) :
    choiceStandardEquiv D w (algebraMap _ _ x) =
      PadicBoundedWittLocalization.inclusion (Arithmetic.residueChar w.1)
        (integerWittEquiv D w x) :=
  (choicePresentationData D w).on_algebraMap x

/-- The actual bounded Witt ring is equivalent to the independent standard ring. -/
def ringEquiv :=
  (choiceEquiv D w).symm.toRingEquiv.trans (choiceStandardEquiv D w)

theorem ringEquiv_algebraMap
    (x : InitialThetaTiltFontaine.Ainf D w) :
    ringEquiv D w (algebraMap _ _ x) =
      algebraMap _ _ (integerWittEquiv D w x) := by
  change choiceStandardEquiv D w
    ((choiceEquiv D w).symm (algebraMap _ _ x)) = _
  rw [(choiceEquiv D w).symm.commutes]
  exact choiceStandardEquiv_algebraMap D w x

theorem ringEquiv_inclusion
    (x : InitialThetaTiltFontaine.Ainf D w) :
    ringEquiv D w (InitialThetaBoundedWittLocalization.inclusion D w x) =
      PadicBoundedWittLocalization.inclusion (Arithmetic.residueChar w.1)
        (integerWittEquiv D w x) :=
  ringEquiv_algebraMap D w x

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
