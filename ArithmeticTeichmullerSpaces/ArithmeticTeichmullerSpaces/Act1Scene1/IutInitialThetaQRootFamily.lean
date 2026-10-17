import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperBallProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootIntegralThreshold
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRootAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullSupportCanonicalAbsLogQ
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQPilotReferenceBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedSupportDefect
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaReferenceCoefficientOrdinaryWeight

/-!
source-id: JT-SCENE1-INITIAL-THETA-QROOT-FAMILY
source: `iut`: `refer/iut/Iut/Concrete/ThetaRegion.lean`, `ThetaLocalData`
and `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`, `thetaLocalData`.
fidelity: constructs the global finite-place q-root family needed by that
interface from the actual torsion-field q-root source. Bad places use the real
root and all other places use `1`; support and nonnegative order are proved.
The concrete local-theory carrier, completion embeddings, and root power law
remain separate source obligations and are not hidden in this family.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open NumberField

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

namespace IutInitialThetaQRootFamily

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def badChars : Finset ℕ :=
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset.image
    Arithmetic.residueChar

def qrootAt (v : NumberField.FinitePlace ↥D.prime.torsionField) :
    v.maximalIdeal.adicCompletion ↥D.prime.torsionField := by
  classical
  exact if hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset then
      (iutInitialThetaOddSupportTorsionQRootSource D).qroot ⟨v, hv⟩
    else 1

theorem qrootAt_ne_zero
    (v : NumberField.FinitePlace ↥D.prime.torsionField) :
    qrootAt D v ≠ 0 := by
  classical
  unfold qrootAt
  split_ifs with hv
  · exact (iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero ⟨v, hv⟩
  · exact one_ne_zero

theorem qrootAt_ordp_nonneg
    (v : NumberField.FinitePlace ↥D.prime.torsionField) :
    0 ≤ Arithmetic.ordp v (qrootAt D v) := by
  classical
  unfold qrootAt
  split_ifs with hv
  ·
    exact Arithmetic.ordp_nonneg_of_norm_le_one v
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot ⟨v, hv⟩)
      (iutInitialThetaFullQRoot_norm_lt_one D ⟨v, hv⟩).le
  · simp [Arithmetic.ordp]

theorem qrootAt_eq_one_of_residueChar_not_mem_badChars
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : Arithmetic.residueChar v ∉ badChars D) :
    qrootAt D v = 1 := by
  classical
  have hnot : v ∉
      (iutInitialThetaOddSupportTorsionQRootSource D).badFinset := by
    intro hmem
    apply hv
    exact Finset.mem_image.mpr ⟨v, hmem, rfl⟩
  simp [qrootAt, hnot]

theorem residueChar_mem_badChars_of_mem_badFinset
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Arithmetic.residueChar v ∈ badChars D := by
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem badChars_prime
    (p : ℕ) (hp : p ∈ badChars D) : p.Prime := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
  exact Arithmetic.residueChar_prime v

theorem qrootAt_pow_eq_of_mem_badFinset
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootAt D v ^ (2 * D.prime.ℓ) =
      (iutInitialThetaOddSupportTorsionQRootSource D).completionMap ⟨v, hv⟩
        ((iutInitialThetaOddSupportBaseQPilotSource D).tateParameter
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace ⟨v, hv⟩)) := by
  unfold qrootAt
  split_ifs with h
  · exact (iutInitialThetaOddSupportTorsionQRootSource D).qroot_pow_eq ⟨v, hv⟩
  · exact (h hv).elim

theorem qrootAt_norm_lt_one_of_mem_badFinset
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖qrootAt D v‖ < 1 := by
  unfold qrootAt
  split_ifs with h
  · exact iutInitialThetaFullQRoot_norm_lt_one D ⟨v, h⟩
  · exact (h hv).elim

theorem qrootAt_pow_eq_admissiblePrime
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hw : ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
      ⟨v, hv⟩).1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    qrootAt D v ^ (2 * D.prime.ℓ) =
      (iutInitialThetaOddSupportTorsionQRootSource D).completionMap ⟨v, hv⟩
        ((D.prime.tate
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace ⟨v, hv⟩).1 hw).q) := by
  unfold qrootAt
  split_ifs with h
  · exact iutInitialThetaOddSupportTorsionQRootSource_qroot_pow_eq_admissiblePrime
      D ⟨v, h⟩ hw
  · exact (h hv).elim

theorem qrootAt_ordp_eq_baseQOrder
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Arithmetic.ordp v (qrootAt D v) =
      ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace ⟨v, hv⟩) : ℝ) /
        (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace ⟨v, hv⟩).1) := by
  unfold qrootAt
  split_ifs with h
  · simpa [PrincipalUnitKummer.baseIntegralThreshold] using
      (PrincipalUnitKummer.qroot_ordp_eq_baseQOrder D ⟨v, h⟩)
  · exact (h hv).elim

noncomputable def qrootAtWeightedFiber
    (p : ℕ) : ℝ := by
  classical
  letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Fintype.ofFinite _
  exact ∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p},
    Arithmetic.placeWeight v.1 *
      (if hv : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset then
        Arithmetic.ordp v.1 (qrootAt D v.1)
      else 0)

theorem qrootAtWeightedFiber_eq_baseQOrder
    (p : ℕ) :
    qrootAtWeightedFiber D p =
      ∑ w ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.attach.filter
          (fun w => Arithmetic.residueChar w.1 = p),
        Arithmetic.qPilotWeight w.1 *
          ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder w : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
  classical
  letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Fintype.ofFinite _
  change (∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p},
    Arithmetic.placeWeight v.1 *
      (if hv : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset then
        Arithmetic.ordp v.1 (qrootAt D v.1)
      else 0)) = _
  calc
    _ = ∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
          Arithmetic.residueChar v = p},
        Arithmetic.placeWeight v.1 *
          (if hv : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset then
            Arithmetic.ordp v.1
              ((iutInitialThetaOddSupportTorsionQRootSource D).qroot ⟨v.1, hv⟩)
          else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases h : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset
      · simp [h, qrootAt]
      · simp [h]
    _ = _ := IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber_eq_baseQOrder D p

theorem qrootAt_log_sum_eq_fullBaseQPilotLogSum :
    ∑ p ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p =
      iutInitialThetaFullBaseQPilotLogSum D := by
  classical
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let term : B.badFinset → ℝ := iutInitialThetaBaseQPilotLogTerm D
  have hfiber (p : ℕ) :
      Real.log p * qrootAtWeightedFiber D p =
        ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p), term ⟨w.1, w.2⟩ := by
    rw [qrootAtWeightedFiber_eq_baseQOrder D p, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    have hp : Arithmetic.residueChar w.1 = p := (Finset.mem_filter.mp hw).2
    simp only [term, iutInitialThetaBaseQPilotLogTerm]
    rw [hp]
    ring
  have hgroup :
      ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
        ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p), term ⟨w.1, w.2⟩ =
        ∑ w : B.badFinset, term w := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩)
      _
  calc
    _ = ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
        ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p), term ⟨w.1, w.2⟩ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hfiber p
    _ = ∑ w : B.badFinset, term w := hgroup
    _ = iutInitialThetaFullBaseQPilotLogSum D := by
      simp [term, iutInitialThetaFullBaseQPilotLogSum, B]

theorem qrootAt_log_sum_eq_selectedWeighted_add_omitted :
    (∑ p ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p) =
      iutInitialThetaSelectedWeightedQRootLogSum D +
        iutInitialThetaOmittedBaseQPilotLogSum D := by
  rw [qrootAt_log_sum_eq_fullBaseQPilotLogSum,
    iutInitialThetaFullBaseQPilotLogSum_eq_selected_add_omitted]

theorem qrootAt_log_sum_eq_selectedWeighted_of_coverage
    (hcover :
      iutInitialThetaOddSupportSelectedBasePlaces D =
        IutOddMultiplicativeSupport D) :
    (∑ p ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p) =
      iutInitialThetaSelectedWeightedQRootLogSum D := by
  rw [qrootAt_log_sum_eq_selectedWeighted_add_omitted,
    (iutInitialThetaOmittedBaseQPilotLogSum_eq_zero_iff_coverage D).mpr hcover,
    add_zero]

theorem qrootAt_log_sum_eq_selectedWeighted_iff_coverage :
    (∑ p ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p) =
      iutInitialThetaSelectedWeightedQRootLogSum D ↔
      iutInitialThetaOddSupportSelectedBasePlaces D =
        IutOddMultiplicativeSupport D := by
  rw [qrootAt_log_sum_eq_selectedWeighted_add_omitted]
  constructor
  · intro hsum
    apply (iutInitialThetaOmittedBaseQPilotLogSum_eq_zero_iff_coverage D).mp
    linarith
  · intro hcover
    rw [(iutInitialThetaOmittedBaseQPilotLogSum_eq_zero_iff_coverage D).mpr hcover,
      add_zero]

def fullSupportRepresentativePaperTerm
    (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  -Real.log (actualPaperRootNorm D
    (iutInitialThetaModuliSelectedSourceEquiv D v).1)

def fullSupportRepresentativeCoefficientDefect : ℝ :=
  ∑ v : iutInitialThetaOddModSupportFinset D,
    (1 - iutInitialThetaRepresentativeCoefficient D v) *
      fullSupportRepresentativePaperTerm D v

theorem selectedPaperSum_eq_qrootFamilySum_add_fullCoefficientDefect :
    iutInitialThetaSelectedQRootPaperSum D =
      (∑ p ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
          Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p) +
        fullSupportRepresentativeCoefficientDefect D := by
  classical
  have hPaper : iutInitialThetaSelectedQRootPaperSum D =
      ∑ v : iutInitialThetaOddModSupportFinset D,
        fullSupportRepresentativePaperTerm D v := by
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    let e := iutInitialThetaModuliSelectedSourceEquiv D
    unfold iutInitialThetaSelectedQRootPaperSum
    calc
      _ = ∑ s : S, -Real.log (actualPaperRootNorm D s.1) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (actualPaperRootNorm_negLog_eq_paperTerm D s.1).symm
      _ = ∑ v : iutInitialThetaOddModSupportFinset D,
          fullSupportRepresentativePaperTerm D v := by
        simpa [fullSupportRepresentativePaperTerm, e] using
          (e.sum_comp (fun s : S => -Real.log (actualPaperRootNorm D s.1))).symm
  have hWeighted : iutInitialThetaFullBaseQPilotLogSum D =
      ∑ v : iutInitialThetaOddModSupportFinset D,
        iutInitialThetaRepresentativeCoefficient D v *
          fullSupportRepresentativePaperTerm D v := by
    rw [iutInitialThetaFullBaseQPilotLogSum_eq_coefficientWeightedPaperSum]
    apply Finset.sum_congr rfl
    intro v hv
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
    change iutInitialThetaRepresentativeCoefficient D v *
        (((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) *
          Real.log (Arithmetic.residueChar s.1)) =
      iutInitialThetaRepresentativeCoefficient D v *
        fullSupportRepresentativePaperTerm D v
    rw [← actualPaperRootNorm_negLog_eq_paperTerm D s]
    rfl
  have hDecomp : iutInitialThetaSelectedQRootPaperSum D =
      iutInitialThetaFullBaseQPilotLogSum D +
        fullSupportRepresentativeCoefficientDefect D := by
    rw [hPaper, hWeighted]
    unfold fullSupportRepresentativeCoefficientDefect
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [hDecomp, qrootAt_log_sum_eq_fullBaseQPilotLogSum]

theorem fullSupportRepresentativeCoefficientDefect_nonneg :
    0 ≤ fullSupportRepresentativeCoefficientDefect D := by
  unfold fullSupportRepresentativeCoefficientDefect
  apply Finset.sum_nonneg
  intro v hv
  have hCoeff := iutInitialThetaRepresentativeCoefficient_mem_Ioc D v
  have hRoot : actualPaperRootNorm D
      (iutInitialThetaModuliSelectedSourceEquiv D v).1 ∈ Set.Ioo (0 : ℝ) 1 :=
    actualPaperRootNorm_mem_Ioo D _
  have hTerm : 0 ≤ fullSupportRepresentativePaperTerm D v :=
    neg_nonneg.mpr (Real.log_nonpos hRoot.1.le hRoot.2.le)
  exact mul_nonneg (sub_nonneg.mpr hCoeff.2) hTerm

theorem fullSupportRepresentativeCoefficientDefect_eq_residueDegreeFormula :
    fullSupportRepresentativeCoefficientDefect D =
      ∑ v : iutInitialThetaOddModSupportFinset D,
        (1 - FullSupportPaperWeightedHull.weight D v *
          ((Arithmetic.inertDeg
              (FullSupportPaperWeightedHull.selected D v).1 : ℝ) /
            Module.finrank ℚ
              ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))) *
          fullSupportRepresentativePaperTerm D v := by
  unfold fullSupportRepresentativeCoefficientDefect
  apply Finset.sum_congr rfl
  intro v hv
  rw [OrdinaryKummerLogHull.representativeCoefficient_eq_ordinaryWeight_mul_sourceInertDeg_ratio]

theorem fullSupportRepresentativeCoefficientDefect_pos_of_exists_lt_one
    (hstrict : ∃ v : iutInitialThetaOddModSupportFinset D,
      iutInitialThetaRepresentativeCoefficient D v < 1) :
    0 < fullSupportRepresentativeCoefficientDefect D := by
  unfold fullSupportRepresentativeCoefficientDefect
  obtain ⟨v₀, hv₀⟩ := hstrict
  have hnonneg (v : iutInitialThetaOddModSupportFinset D) :
      0 ≤ (1 - iutInitialThetaRepresentativeCoefficient D v) *
        fullSupportRepresentativePaperTerm D v := by
    have hCoeff := iutInitialThetaRepresentativeCoefficient_mem_Ioc D v
    have hRoot : actualPaperRootNorm D
        (iutInitialThetaModuliSelectedSourceEquiv D v).1 ∈ Set.Ioo (0 : ℝ) 1 :=
      actualPaperRootNorm_mem_Ioo D _
    exact mul_nonneg (sub_nonneg.mpr hCoeff.2)
      (neg_nonneg.mpr (Real.log_nonpos hRoot.1.le hRoot.2.le))
  have hpos : 0 <
      (1 - iutInitialThetaRepresentativeCoefficient D v₀) *
        fullSupportRepresentativePaperTerm D v₀ := by
    have hRoot : actualPaperRootNorm D
        (iutInitialThetaModuliSelectedSourceEquiv D v₀).1 ∈ Set.Ioo (0 : ℝ) 1 :=
      actualPaperRootNorm_mem_Ioo D _
    exact mul_pos (sub_pos.mpr hv₀)
      (neg_pos.mpr (Real.log_neg hRoot.1 hRoot.2))
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (fun v _ => hnonneg v) (Finset.mem_univ v₀))

theorem fullSupportRepresentativeCoefficientDefect_pos_of_vbad_nonempty :
    0 < fullSupportRepresentativeCoefficientDefect D := by
  apply fullSupportRepresentativeCoefficientDefect_pos_of_exists_lt_one D
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  have hvOdd : v ∈ iutVBadOddModSupportPort D :=
    iutInitialThetaVBad_subset_VBadOdd D hv
  let vFull : iutInitialThetaOddModSupportFinset D :=
    ⟨v, (iutInitialThetaOddModSupport_finite D).mem_toFinset.mpr (by
      exact hvOdd)⟩
  refine ⟨vFull, ?_⟩
  exact iutInitialThetaRepresentativeCoefficient_lt_one_on_vbad D vFull hv

theorem qrootAt_log_sum_le_selectedPaperSum :
    (∑ p ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p) ≤
      iutInitialThetaSelectedQRootPaperSum D := by
  rw [qrootAt_log_sum_eq_fullBaseQPilotLogSum]
  exact iutInitialThetaFullBaseQPilotLogSum_le_selectedPaperSum D

theorem qrootAt_log_sum_lt_selectedPaperSum :
    (∑ p ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p) <
      iutInitialThetaSelectedQRootPaperSum D := by
  rw [qrootAt_log_sum_eq_fullBaseQPilotLogSum]
  exact iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum D

theorem qrootAt_log_sum_eq_selectedPaperSum_iff_coefficients_eq_one :
    (∑ p ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p) =
      iutInitialThetaSelectedQRootPaperSum D ↔
      ∀ v : iutInitialThetaOddModSupportFinset D,
        iutInitialThetaRepresentativeCoefficient D v = 1 := by
  rw [qrootAt_log_sum_eq_fullBaseQPilotLogSum]
  exact iutInitialThetaFullBaseQPilotLogSum_eq_paperSum_iff_coefficients_eq_one D

theorem qrootAt_log_sum_eq_iut_absLogQ_of_support_eq
    (hSupport : IutOddMultiplicativeSupport D =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    let B := iutInitialThetaOddSupportBaseQPilotSource D
    ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
        Real.log p * qrootAtWeightedFiber D p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  classical
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  have hFamily :=
    iutInitialThetaOddSupportWeighted_logSum_eq_reference_absLogQ_of_support_eq
      D hSupport
  have hFiber (p : ℕ) :
      qrootAtWeightedFiber D p =
        IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
    rw [qrootAtWeightedFiber_eq_baseQOrder,
      IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber_eq_baseQOrder]
  change ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
      Real.log p * qrootAtWeightedFiber D p = _
  calc
    _ = ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
        Real.log p *
          IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hFiber]
    _ = _ := by simpa [B] using hFamily

theorem qrootAt_log_sum_eq_canonical_qPilot_absLogQ_of_support_eq
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (hEll : T.ell = D.prime.ℓ)
    (hLink : T.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength)
    (hSupport : IutOddMultiplicativeSupport D =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    let hCompat : QNormTateCompatibility T.scene1.data.link := by
      rw [hLink]
      exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase
        packetHull heightData ramification logVolume processionLength
    let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
      packetHull heightData ramification logVolume processionLength hEll hLink
    ∑ q ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar,
        Real.log q * qrootAtWeightedFiber D q =
      (S.toSceneQPilot p hCompat).absLogQ p := by
  let hCompat : QNormTateCompatibility T.scene1.data.link := by
    rw [hLink]
    exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase
      packetHull heightData ramification logVolume processionLength
  let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
    packetHull heightData ramification logVolume processionLength hEll hLink
  have hFamily := qrootAt_log_sum_eq_iut_absLogQ_of_support_eq D hSupport
  have hReference :=
    Corollary312QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
      p D theta thetaBase packetHull heightData ramification logVolume processionLength
      hEll hLink
  change ∑ q ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
      Arithmetic.residueChar,
      Real.log q * qrootAtWeightedFiber D q =
    (S.toSceneQPilot p hCompat).absLogQ p
  exact hFamily.trans hReference.symm

theorem qrootAt_log_sum_eq_vbadCoefficientWeightedPaperSum_of_support_eq
    (hSupport : IutOddMultiplicativeSupport D =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    let B := iutInitialThetaOddSupportBaseQPilotSource D
    ∑ q ∈ B.badFinset.image Arithmetic.residueChar,
        Real.log q * qrootAtWeightedFiber D q =
      ∑ v : iutInitialThetaVBadModuliFinset D,
        iutInitialThetaRepresentativeCoefficient D
            (iutInitialThetaVBadModuliAt D v) *
          VBadSelectedPaper.paperTerm D v := by
  classical
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  have hFamily := qrootAt_log_sum_eq_iut_absLogQ_of_support_eq D hSupport
  have hPaper := VBadSelectedPaper.referenceAbsLogQ_eq_coefficientWeightedPaperSum D
  change ∑ q ∈ B.badFinset.image Arithmetic.residueChar,
      Real.log q * qrootAtWeightedFiber D q = _
  exact hFamily.trans hPaper

def vbadRepresentativeCoefficientDefect : ℝ :=
  ∑ v : iutInitialThetaVBadModuliFinset D,
    (1 - iutInitialThetaRepresentativeCoefficient D
        (iutInitialThetaVBadModuliAt D v)) *
      VBadSelectedPaper.paperTerm D v

theorem fullPaperSum_eq_qrootFamilySum_add_defects_of_support_eq
    (hSupport : IutOddMultiplicativeSupport D =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    iutInitialThetaSelectedQRootPaperSum D =
      (∑ q ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
          Arithmetic.residueChar,
        Real.log q * qrootAtWeightedFiber D q) +
        vbadRepresentativeCoefficientDefect D +
          JoshiTeich.Act1Scene1.VBadSelectedPaper.omittedPaperSum D := by
  classical
  let wsum : ℝ := ∑ v : iutInitialThetaVBadModuliFinset D,
    iutInitialThetaRepresentativeCoefficient D
        (iutInitialThetaVBadModuliAt D v) *
      VBadSelectedPaper.paperTerm D v
  have hPaperUnweighted :
      JoshiTeich.Act1Scene1.VBadSelectedPaper.paperSum D =
        ∑ v : iutInitialThetaVBadModuliFinset D,
          JoshiTeich.Act1Scene1.VBadSelectedPaper.paperTerm D v := by
    calc
      JoshiTeich.Act1Scene1.VBadSelectedPaper.paperSum D =
          ∑ s : ↥(JoshiTeich.Act1Scene1.VBadSelectedPaper.selectedFinset D),
            -Real.log (actualPaperRootNorm D s.1) :=
        JoshiTeich.Act1Scene1.VBadSelectedPaper.paperSum_eq_selectedRootLogSum D
      _ = ∑ v : iutInitialThetaVBadModuliFinset D,
          JoshiTeich.Act1Scene1.VBadSelectedPaper.paperTerm D v := by
        simpa [JoshiTeich.Act1Scene1.VBadSelectedPaper.paperTerm,
          JoshiTeich.Act1Scene1.VBadSelectedPaper.sourceAt,
          JoshiTeich.Act1Scene1.VBadSelectedPaper.sourceEquiv] using
          ((JoshiTeich.Act1Scene1.VBadSelectedPaper.sourceEquiv D).sum_comp
            (fun s : ↥(JoshiTeich.Act1Scene1.VBadSelectedPaper.selectedFinset D) =>
              -Real.log (actualPaperRootNorm D s.1))).symm
  have hPaperSum : VBadSelectedPaper.paperSum D =
      wsum + vbadRepresentativeCoefficientDefect D := by
    rw [hPaperUnweighted]
    unfold wsum vbadRepresentativeCoefficientDefect
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have hFamily :=
    qrootAt_log_sum_eq_vbadCoefficientWeightedPaperSum_of_support_eq D hSupport
  have hFamily' :
      (∑ q ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
        Arithmetic.residueChar, Real.log q * qrootAtWeightedFiber D q) = wsum := by
    simpa [wsum] using hFamily
  calc
    iutInitialThetaSelectedQRootPaperSum D =
        JoshiTeich.Act1Scene1.VBadSelectedPaper.paperSum D +
          JoshiTeich.Act1Scene1.VBadSelectedPaper.omittedPaperSum D :=
      JoshiTeich.Act1Scene1.VBadSelectedPaper.fullPaperSum_eq_selected_add_omitted D
    _ = wsum + vbadRepresentativeCoefficientDefect D +
          JoshiTeich.Act1Scene1.VBadSelectedPaper.omittedPaperSum D := by
      rw [hPaperSum]
    _ = _ := by rw [hFamily'.symm]

theorem vbadRepresentativeCoefficientDefect_nonneg :
    0 ≤ vbadRepresentativeCoefficientDefect D := by
  unfold vbadRepresentativeCoefficientDefect
  apply Finset.sum_nonneg
  intro v hv
  have hCoeff := iutInitialThetaRepresentativeCoefficient_mem_Ioc D
    (iutInitialThetaVBadModuliAt D v)
  exact mul_nonneg (sub_nonneg.mpr hCoeff.2)
    (VBadSelectedPaper.paperTerm_pos D v).le

end IutInitialThetaQRootFamily

end
end JoshiTeich.Act1Scene1
