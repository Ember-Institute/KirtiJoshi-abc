import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogarithmSeries
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusExpansion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFontaineKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-LOGARITHM
source: Joshi II `se:ff-rings`, `eq:tate-module-of-lubin-tate` and
`pr:teichmuller-lift-A/B`, the logarithm of the multiplicative Tate tower.
fidelity: bounds every actual integral Fontaine-kernel element in each
rho norm using its original Teichmuller constant coefficient and p-tail.
Thus the original Tate coordinate [epsilon]-1 is in the proved log
convergence domain. Defines its actual convergent logarithm in the
common complete ring and transports it through the actual Frobenius.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; logarithmic power identities, nonvanishing,
the phi=p eigenspace and paper B/period/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateLogarithm

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittLogarithmSeries
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Ainf := InitialThetaTiltFontaine.Ainf D w
abbrev Tate := InitialThetaCyclotomicTateTilt.Tate D w

theorem norm_ainf_teichmuller (ρ : Radius) (a : InitialThetaTiltIntegers.Integers D w) :
    ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (WittVector.teichmuller (Arithmetic.residueChar w.1) a)‖ =
      ‖a‖ := by
  rw [InitialThetaWittRhoExpansion.ainfMap, RingHom.comp_apply,
    InitialThetaWittRhoCompletion.inclusion_norm, InitialThetaWittRhoNorm.realValue,
    InitialThetaWittRhoValue.value_inclusion D w ρ.val ρ.property.1.ne'
      (ρ.property.2.trans ENNReal.one_lt_top).ne]
  simp only [InitialThetaBoundedWittExpansion.wittInclusion, WittVector.map_teichmuller,
    WittWeightedDigits.value_teichmuller, ENNReal.toReal_ofReal (norm_nonneg _)]
  rfl

theorem norm_ainf_kernel_le (ρ : Radius) (a : Ainf D w) (ha : InitialThetaTiltFontaine.theta D w a = 0) :
    ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a‖ ≤
      max ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖
        ρ.val.toReal := by
  obtain ⟨b, hb⟩ := InitialThetaFontaineKernel.decomposition D w a
  rw [hb, map_add, map_mul]
  apply (InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _).trans
  apply max_le_max
  · rw [norm_ainf_teichmuller]
    exact InitialThetaFontaineKernel.constantCoeff_norm_le D w a ha
  · calc
      _ ≤ ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (Arithmetic.residueChar w.1)‖ *
          ‖InitialThetaWittRhoExpansion.ainfMap D w ρ b‖ := norm_mul_le _ _
      _ ≤ ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (Arithmetic.residueChar w.1)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (InitialThetaWittRhoExpansion.norm_ainfMap_le_one D w ρ b)
      _ = _ := InitialThetaWittRhoExpansion.norm_ainfMap_prime D w ρ

theorem norm_ainf_kernel_lt_one (ρ : Radius) (a : Ainf D w)
    (ha : InitialThetaTiltFontaine.theta D w a = 0) :
    ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a‖ < 1 := by
  apply (norm_ainf_kernel_le D w ρ a ha).trans_lt
  apply max_lt
  · exact (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2
  · simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
        ρ.property.2

theorem coordinate_kernel_lt_one (a : Ainf D w) (ha : InitialThetaTiltFontaine.theta D w a = 0)
    (ρ : Radius) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (InitialThetaWittAllRadiusExpansion.ainfMap D w a) < 1 :=
  norm_ainf_kernel_lt_one D w ρ a ha

def coordinate (t : Tate D w) : Carrier D w :=
  InitialThetaWittAllRadiusExpansion.ainfMap D w (InitialThetaCyclotomicTateTilt.kernelCoordinate D w t)

theorem coordinate_lt_one (t : Tate D w) (ρ : Radius) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (coordinate D w t) < 1 :=
  coordinate_kernel_lt_one D w _ (InitialThetaCyclotomicTateTilt.kernelCoordinate_mem_ker D w t) ρ

def tateLog (t : Tate D w) : Carrier D w := logOneAdd D w (coordinate D w t)

theorem summable_tateLog (t : Tate D w) : Summable (logTerm D w (coordinate D w t)) :=
  summable_logTerm D w _ (coordinate_lt_one D w t)

theorem hasSum_tateLog (t : Tate D w) :
    HasSum (logTerm D w (coordinate D w t)) (tateLog D w t) :=
  hasSum_logOneAdd D w _ (coordinate_lt_one D w t)

theorem frobenius_coordinate (t : Tate D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (coordinate D w t) =
      coordinate D w (t ^ Arithmetic.residueChar w.1) := by
  change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
    (InitialThetaWittAllRadiusCompletion.inclusion D w
      (InitialThetaBoundedWittLocalization.inclusion D w _)) = _
  rw [InitialThetaWittAllRadiusFrobenius.frobenius_inclusion]
  change InitialThetaWittAllRadiusCompletion.inclusion D w
    (InitialThetaBoundedWittLocalization.frobenius D w
      (InitialThetaBoundedWittLocalization.inclusion D w _)) = _
  rw [InitialThetaBoundedWittLocalization.frobenius_inclusion]
  exact congrArg (InitialThetaWittAllRadiusExpansion.ainfMap D w)
    (InitialThetaTateFrobenius.phi_kernelCoordinate D w t)

theorem frobenius_tateLog (t : Tate D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (tateLog D w t) =
      tateLog D w (t ^ Arithmetic.residueChar w.1) := by
  change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
    (logOneAdd D w (coordinate D w t)) = _
  rw [frobenius_logOneAdd D w _ (coordinate_lt_one D w t), frobenius_coordinate]
  rfl

theorem tateLog_one : tateLog D w 1 = 0 := by
  have hc : coordinate D w 1 = 0 := by
    rw [coordinate, InitialThetaCyclotomicTateTilt.kernelCoordinate_one, map_zero]
  rw [tateLog, hc, logOneAdd_zero]

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateLogarithm
