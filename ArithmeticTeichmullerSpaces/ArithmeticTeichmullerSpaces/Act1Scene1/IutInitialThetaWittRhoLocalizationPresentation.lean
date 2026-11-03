import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoValue
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoValue
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-LOCALIZATION-PRESENTATION
source: Joshi II `se:ff-rings`, the bounded Away localization presentation,
and the proved p-power presentation in the fraction Witt carrier.
fidelity: rewrites the existing rho value as the weighted numerator value
divided by the value of the chosen bounded denominator. This keeps the
comparison on the algebraic localized carriers and does not identify paper B.
Original proof; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoValue

open JoshiTeich.Prologue
open InitialThetaBoundedWittExpansion InitialThetaBoundedWittLocalization
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeLocalizationPresentation : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

local instance coefficientFieldLocalizationPresentation : Field (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltField.carrierField D w

local instance normedFieldLocalizationPresentation : NormedField (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltTopology.carrierNormedField D w

local instance perfectLocalizationPresentation : PerfectRing
    (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1) :=
  InitialThetaTiltField.carrierPerfect D w

theorem value_eq_of_choice_presentation
    (s : InitialThetaTiltIntegers.Integers D w) (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1)
    (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w s)
    (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w)
    (hx : x * algebraMap _ _ (InitialThetaWittLocalizationChoice.choiceDenominator D w s) ^ m =
      algebraMap _ _ a) :
    value D w ρ (InitialThetaWittLocalizationChoice.toCanonical D w s hs0 x) =
      WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ (wittInclusion D w a) /
        (ρ * ENNReal.ofReal ‖s‖) ^ m := by
  let p := Arithmetic.residueChar w.1
  let v : InitialThetaTiltField.Carrier D w := s
  let r : InitialThetaTiltField.Carrier D w := (v ^ m)⁻¹
  have hv : v ≠ 0 := Subtype.coe_ne_coe.mpr hs0
  have hden : ambientInclusion D w
      (InitialThetaWittLocalizationChoice.choiceDenominator D w s) =
      (p : Ambient D w) *
        algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller p v) := by
    simp only [InitialThetaWittLocalizationChoice.choiceDenominator, map_mul, map_natCast,
      ambientInclusion, RingHom.comp_apply, wittInclusion, WittVector.map_teichmuller]
    rfl
  have hc := congrArg (InitialThetaWittLocalizationChoice.toCanonical D w s hs0) hx
  simp only [map_mul, map_pow] at hc
  rw [InitialThetaWittLocalizationChoice.toCanonical_inclusion D w s hs0,
    InitialThetaWittLocalizationChoice.toCanonical_inclusion D w s hs0] at hc
  have he := congrArg (toAmbient D w) hc
  simp only [map_mul, map_pow] at he
  change toAmbient D w (InitialThetaWittLocalizationChoice.toCanonical D w s hs0 x) *
      toAmbient D w (inclusion D w (InitialThetaWittLocalizationChoice.choiceDenominator D w s)) ^ m =
    toAmbient D w (inclusion D w a) at he
  rw [toAmbient_inclusion, toAmbient_inclusion, hden] at he
  have hteich : WittVector.teichmuller p v ≠ 0 := by
    intro h
    have hc := congrArg (fun b : FieldWitt D w => b.coeff 0) h
    exact hv (by simpa only [WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] using hc)
  have hteichImage : algebraMap (FieldWitt D w) (Ambient D w)
      (WittVector.teichmuller p v) ≠ 0 := by
    intro h
    exact hteich (IsFractionRing.injective (FieldWitt D w) (Ambient D w)
      (h.trans (map_zero _).symm))
  let y : FieldWitt D w := WittVector.teichmuller p r * wittInclusion D w a
  have hteichInv : WittVector.teichmuller p r * WittVector.teichmuller p v ^ m = 1 := by
    calc
      WittVector.teichmuller p r * WittVector.teichmuller p v ^ m =
          WittVector.teichmuller p (r * v ^ m) := by rw [map_mul, map_pow]
      _ = WittVector.teichmuller p 1 := by
        congr 1
        exact inv_mul_cancel₀ (pow_ne_zero m hv)
      _ = 1 := map_one _
  have hy :
      toAmbient D w (InitialThetaWittLocalizationChoice.toCanonical D w s hs0 x) *
        (p : Ambient D w) ^ m = algebraMap (FieldWitt D w) (Ambient D w) y := by
    apply mul_right_cancel₀ (pow_ne_zero m hteichImage)
    calc
      (toAmbient D w (InitialThetaWittLocalizationChoice.toCanonical D w s hs0 x) *
          (p : Ambient D w) ^ m) *
          algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller p v) ^ m =
          ambientInclusion D w a := by
        calc
          _ = toAmbient D w (InitialThetaWittLocalizationChoice.toCanonical D w s hs0 x) *
              ((p : Ambient D w) *
                algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller p v)) ^ m := by
            rw [mul_pow]
            ring
          _ = ambientInclusion D w a := he
      _ = algebraMap (FieldWitt D w) (Ambient D w) y *
          algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller p v) ^ m := by
        rw [← map_pow, ← map_mul]
        change algebraMap (FieldWitt D w) (Ambient D w) (wittInclusion D w a) =
          algebraMap (FieldWitt D w) (Ambient D w)
            (y * WittVector.teichmuller p v ^ m)
        apply congrArg (algebraMap (FieldWitt D w) (Ambient D w))
        change wittInclusion D w a = y * WittVector.teichmuller p v ^ m
        change wittInclusion D w a =
          (WittVector.teichmuller p r * wittInclusion D w a) *
            WittVector.teichmuller p v ^ m
        calc
          wittInclusion D w a =
              (WittVector.teichmuller p r * WittVector.teichmuller p v ^ m) *
                wittInclusion D w a := by rw [hteichInv, one_mul]
          _ = (WittVector.teichmuller p r * wittInclusion D w a) *
                WittVector.teichmuller p v ^ m := by ac_rfl
  have hvalue := value_eq_of_presentation D w ρ hρ0 hρtop
    (InitialThetaWittLocalizationChoice.toCanonical D w s hs0 x) m y hy
  rw [hvalue, WittWeightedDigits.value_teichmuller_mul]
  have hnorm : ‖r‖ = ‖v‖⁻¹ ^ m := by
    change ‖(v ^ m)⁻¹‖ = ‖v‖⁻¹ ^ m
    rw [norm_inv, norm_pow]
    exact (inv_pow ‖v‖ m).symm
  rw [hnorm]
  have hnormPos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnormENN : ENNReal.ofReal ‖v‖ ≠ 0 ∧ ENNReal.ofReal ‖v‖ ≠ ⊤ := by
    exact ⟨ne_of_gt (ENNReal.ofReal_pos.mpr hnormPos), ENNReal.ofReal_ne_top⟩
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr (norm_nonneg _)) m,
    ENNReal.ofReal_inv_of_pos hnormPos]
  apply (ENNReal.div_eq_div_iff
    (pow_ne_zero m (mul_ne_zero hρ0 hnormENN.1))
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top hρtop hnormENN.2))
    (pow_ne_zero m hρ0) (ENNReal.pow_ne_top hρtop)).mpr
  have hcancel : (ENNReal.ofReal ‖v‖) ^ m *
      (ENNReal.ofReal ‖v‖)⁻¹ ^ m = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hnormENN.1 hnormENN.2, one_pow]
  calc
    (ρ * ENNReal.ofReal ‖v‖) ^ m *
        ((ENNReal.ofReal ‖v‖)⁻¹ ^ m *
          WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ (wittInclusion D w a)) =
      ρ ^ m * ((ENNReal.ofReal ‖v‖ ^ m *
          (ENNReal.ofReal ‖v‖)⁻¹ ^ m) *
        WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ (wittInclusion D w a)) := by
          rw [mul_pow]
          ac_rfl
    _ = ρ ^ m * WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ
        (wittInclusion D w a) := by rw [hcancel, one_mul]

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoValue

namespace JoshiTeich.Act1Scene1.PadicWittRhoValue

open PadicBoundedWittExpansion PadicBoundedWittLocalization
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]

local instance rawCoefficientField : Field (PadicTiltField.Carrier p) :=
  FractionRing.field (PadicTiltField.Source p)

private theorem denominator_image_value (ρ : ℝ≥0∞) :
    WittWeightedDigits.value p ρ (wittInclusion p (denominator p)) =
      ρ * ENNReal.ofReal ‖contraction p‖ := by
  simp only [denominator, WittPrimeTeichLocalization.denominator, map_mul, map_natCast,
    wittInclusion, WittVector.map_teichmuller]
  rw [mul_comm (p : FieldWitt p) _,
    WittWeightedDigits.value_mul_prime, WittWeightedDigits.value_teichmuller]
  rfl

theorem value_eq_of_away_presentation
    (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : PadicBoundedWittLocalization.Ring p)
    (m : ℕ) (a : PadicBoundedWittLocalization.Ainf p)
    (hx : x * inclusion p (denominator p) ^ m = inclusion p a) :
    value p ρ x =
      WittWeightedDigits.value p ρ (wittInclusion p a) /
        (ρ * ENNReal.ofReal ‖contraction p‖) ^ m := by
  let v : PadicTiltField.Carrier p := contraction p
  let r : PadicTiltField.Carrier p := (v ^ m)⁻¹
  have hv : v ≠ 0 := Subtype.coe_ne_coe.mpr (contraction_ne_zero p)
  have hden : ambientInclusion p (denominator p) =
      (p : Ambient p) *
        algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v) := by
    simp only [denominator, WittPrimeTeichLocalization.denominator, map_mul, map_natCast,
      ambientInclusion, RingHom.comp_apply, wittInclusion, WittVector.map_teichmuller]
    rfl
  have he := congrArg (toAmbient p) hx
  simp only [map_mul, map_pow] at he
  change toAmbient p x * toAmbient p (inclusion p (denominator p)) ^ m =
    toAmbient p (inclusion p a) at he
  rw [toAmbient_inclusion, toAmbient_inclusion, hden] at he
  have hteich : WittVector.teichmuller p v ≠ 0 := by
    intro h
    have hc := congrArg (fun b : FieldWitt p => b.coeff 0) h
    exact hv (by simpa only [WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] using hc)
  have hteichImage : algebraMap (FieldWitt p) (Ambient p)
      (WittVector.teichmuller p v) ≠ 0 := by
    intro h
    exact hteich (IsFractionRing.injective (FieldWitt p) (Ambient p)
      (h.trans (map_zero _).symm))
  let y : FieldWitt p := WittVector.teichmuller p r * wittInclusion p a
  have hteichInv : WittVector.teichmuller p r * WittVector.teichmuller p v ^ m = 1 := by
    calc
      WittVector.teichmuller p r * WittVector.teichmuller p v ^ m =
          WittVector.teichmuller p (r * v ^ m) := by rw [map_mul, map_pow]
      _ = WittVector.teichmuller p 1 := by
        congr 1
        exact inv_mul_cancel₀ (pow_ne_zero m hv)
      _ = 1 := map_one _
  have hy : toAmbient p x * (p : Ambient p) ^ m =
      algebraMap (FieldWitt p) (Ambient p) y := by
    apply mul_right_cancel₀ (pow_ne_zero m hteichImage)
    calc
      (toAmbient p x * (p : Ambient p) ^ m) *
          algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v) ^ m =
          ambientInclusion p a := by
        calc
          _ = toAmbient p x * ((p : Ambient p) *
              algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v)) ^ m := by
            rw [mul_pow]
            ring
          _ = ambientInclusion p a := he
      _ = algebraMap (FieldWitt p) (Ambient p) y *
          algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v) ^ m := by
        rw [← map_pow, ← map_mul]
        change algebraMap (FieldWitt p) (Ambient p) (wittInclusion p a) =
          algebraMap (FieldWitt p) (Ambient p)
            (y * WittVector.teichmuller p v ^ m)
        apply congrArg (algebraMap (FieldWitt p) (Ambient p))
        change wittInclusion p a = y * WittVector.teichmuller p v ^ m
        change wittInclusion p a =
          (WittVector.teichmuller p r * wittInclusion p a) *
            WittVector.teichmuller p v ^ m
        calc
          wittInclusion p a =
              (WittVector.teichmuller p r * WittVector.teichmuller p v ^ m) *
                wittInclusion p a := by rw [hteichInv, one_mul]
          _ = (WittVector.teichmuller p r * wittInclusion p a) *
                WittVector.teichmuller p v ^ m := by ac_rfl
  have hvalue := value_eq_of_presentation p ρ hρ0 hρtop x m y hy
  rw [hvalue, WittWeightedDigits.value_teichmuller_mul]
  have hnorm : ‖r‖ = ‖v‖⁻¹ ^ m := by
    change ‖(v ^ m)⁻¹‖ = ‖v‖⁻¹ ^ m
    rw [norm_inv, norm_pow]
    exact (inv_pow ‖v‖ m).symm
  rw [hnorm]
  have hnormPos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnormENN : ENNReal.ofReal ‖v‖ ≠ 0 ∧ ENNReal.ofReal ‖v‖ ≠ ⊤ := by
    exact ⟨ne_of_gt (ENNReal.ofReal_pos.mpr hnormPos), ENNReal.ofReal_ne_top⟩
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr (norm_nonneg _)) m,
    ENNReal.ofReal_inv_of_pos hnormPos]
  apply (ENNReal.div_eq_div_iff
    (pow_ne_zero m (mul_ne_zero hρ0 hnormENN.1))
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top hρtop hnormENN.2))
    (pow_ne_zero m hρ0) (ENNReal.pow_ne_top hρtop)).mpr
  have hcancel : (ENNReal.ofReal ‖v‖) ^ m *
      (ENNReal.ofReal ‖v‖)⁻¹ ^ m = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hnormENN.1 hnormENN.2, one_pow]
  calc
    (ρ * ENNReal.ofReal ‖v‖) ^ m *
        ((ENNReal.ofReal ‖v‖)⁻¹ ^ m *
          WittWeightedDigits.value p ρ (wittInclusion p a)) =
      ρ ^ m * ((ENNReal.ofReal ‖v‖ ^ m *
          (ENNReal.ofReal ‖v‖)⁻¹ ^ m) *
        WittWeightedDigits.value p ρ (wittInclusion p a)) := by
          rw [mul_pow]
          ac_rfl
    _ = ρ ^ m * WittWeightedDigits.value p ρ (wittInclusion p a) := by
      rw [hcancel, one_mul]

end
end JoshiTeich.Act1Scene1.PadicWittRhoValue
