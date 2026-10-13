import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullRepresentativeBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-COEFFICIENTS
source: complete moduli j-log accounting, the actual section equivalence,
selected q-root ordp, and the base/source ramification tower.
fidelity: computes every coefficient of the full normalized q-pilot on the
actual selected representatives. Equality with the unweighted paper sum
requires all these coefficients to be one; this condition is not assumed.
Paper carrier identity and theta-volume construction remain separate.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

def iutInitialThetaRepresentativeCoefficient
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
  let b := R.basePlace s
  Arithmetic.qPilotWeight v.1 /
    ((Arithmetic.relRamIdx b.1 v.1 : ℝ) * Arithmetic.relRamIdx s.1 b.1)

private def paperTerm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
  ((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) *
    Real.log (Arithmetic.residueChar s.1)

private theorem paperTerm_pos
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddModSupportFinset D) : 0 < paperTerm D v := by
  let hv := (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v.1 hv
  let b := R.basePlace s
  have hOrd := iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder D v.1 hv
  have hq : (0 : ℝ) < B.qOrder b := by exact_mod_cast B.qOrder_pos b
  have he : (0 : ℝ) < D.prime.ℓ := by
    exact_mod_cast Nat.lt_of_lt_of_le (by decide : 0 < 5) D.prime.five_le
  have hb : (0 : ℝ) < Arithmetic.ramIdx b.1 := by
    exact_mod_cast Arithmetic.ramIdx_pos b.1
  have hs : (0 : ℝ) < Arithmetic.ramIdx s.1 := by
    exact_mod_cast Arithmetic.ramIdx_pos s.1
  have hp : 0 < Real.log (Arithmetic.residueChar s.1) := by
    apply Real.log_pos
    exact_mod_cast (Arithmetic.residueChar_prime s.1).one_lt
  change 0 < ((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) *
    Real.log (Arithmetic.residueChar s.1)
  rw [hOrd]
  positivity

theorem iutInitialThetaModuliJLogTerm_eq_coefficient_mul_selectedPaperTerm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddModSupportFinset D) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
    Real.log ‖NumberField.FinitePlace.embedding v.1.maximalIdeal
      (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
        ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖ /
      (2 * (D.prime.ℓ : ℝ) *
        (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) =
      iutInitialThetaRepresentativeCoefficient D v *
        (((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) *
          Real.log (Arithmetic.residueChar s.1)) := by
  let hv := (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v.1 hv
  let b := R.basePlace s
  have hOrd := iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder D v.1 hv
  change Arithmetic.ordp s.1 (R.qroot s) =
    (B.qOrder b : ℝ) / (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx b.1) at hOrd
  have hRam : (Arithmetic.ramIdx s.1 : ℝ) =
      (Arithmetic.ramIdx b.1 : ℝ) * Arithmetic.relRamIdx s.1 b.1 := by
    exact_mod_cast Arithmetic.ramIdx_eq_mul (R.liesOver s)
  have hb : (Arithmetic.ramIdx b.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.ramIdx_pos b.1).ne'
  have hr : (Arithmetic.relRamIdx s.1 b.1 : ℝ) ≠ 0 := by
    exact_mod_cast Arithmetic.relRamIdx_ne_zero (R.liesOver s)
  rw [iutInitialThetaModuliJLogTerm_eq_weightedBaseQOrder D v.1 v.2]
  change (Arithmetic.qPilotWeight v.1 / (Arithmetic.relRamIdx b.1 v.1 : ℝ)) *
      ((B.qOrder b : ℝ) / (2 * (D.prime.ℓ : ℝ))) * Real.log (Arithmetic.residueChar b.1) =
    (Arithmetic.qPilotWeight v.1 /
      ((Arithmetic.relRamIdx b.1 v.1 : ℝ) * Arithmetic.relRamIdx s.1 b.1)) *
        (((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) *
          Real.log (Arithmetic.residueChar s.1))
  rw [hOrd, hRam, Arithmetic.residueChar_eq_of_liesOver (R.liesOver s)]
  field_simp [hb, hr]
  <;> ring

theorem iutInitialThetaRepresentativeCoefficient_mem_Ioc
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddModSupportFinset D) :
    iutInitialThetaRepresentativeCoefficient D v ∈ Set.Ioc (0 : ℝ) 1 := by
  let hv := (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v.1 hv
  let b := R.basePlace s
  have hb : b.1 = iutInitialThetaSectionBasePlace D v.1 :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v.1 hv
  have hbv : Ideal.LiesOver b.1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal := by
    rw [hb]
    exact iutInitialThetaSectionBasePlace_liesOver D v.1
  have he : (0 : ℝ) < Arithmetic.relRamIdx b.1 v.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (Arithmetic.relRamIdx_ne_zero hbv)
  have hr : (0 : ℝ) < Arithmetic.relRamIdx s.1 b.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (Arithmetic.relRamIdx_ne_zero (R.liesOver s))
  refine ⟨?_, ?_⟩
  · change 0 < Arithmetic.qPilotWeight v.1 /
      ((Arithmetic.relRamIdx b.1 v.1 : ℝ) * Arithmetic.relRamIdx s.1 b.1)
    exact div_pos (Arithmetic.qPilotWeight_pos v.1) (mul_pos he hr)
  · have h := iutInitialThetaModuliJLogTerm_le_selectedPaperTerm D v
    rw [iutInitialThetaModuliJLogTerm_eq_coefficient_mul_selectedPaperTerm D v] at h
    change iutInitialThetaRepresentativeCoefficient D v * paperTerm D v ≤ paperTerm D v at h
    exact le_of_mul_le_mul_of_pos_right (by simpa only [one_mul] using h)
      (paperTerm_pos D v)

theorem iutInitialThetaFullBaseQPilotLogSum_eq_coefficientWeightedPaperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaFullBaseQPilotLogSum D =
      ∑ v : iutInitialThetaOddModSupportFinset D,
        let R := iutInitialThetaOddSupportTorsionQRootSource D
        let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
        iutInitialThetaRepresentativeCoefficient D v *
          (((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) *
            Real.log (Arithmetic.residueChar s.1)) := by
  rw [iutInitialThetaFullBaseQPilotLogSum_eq_moduliJLogSum, Finset.sum_div]
  rw [← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl fun v _ =>
    iutInitialThetaModuliJLogTerm_eq_coefficient_mul_selectedPaperTerm D v

private theorem paperSum_eq_sum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaSelectedQRootPaperSum D =
      ∑ v : iutInitialThetaOddModSupportFinset D, paperTerm D v := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  exact (iutInitialThetaModuliSelectedSourceEquiv D).sum_comp
    (fun s : S => ((Arithmetic.ramIdx s.1.1 : ℝ) * Arithmetic.ordp s.1.1 (R.qroot s.1)) *
      Real.log (Arithmetic.residueChar s.1.1)) |>.symm

theorem iutInitialThetaFullBaseQPilotLogSum_eq_paperSum_iff_coefficients_eq_one
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaFullBaseQPilotLogSum D = iutInitialThetaSelectedQRootPaperSum D ↔
      ∀ v : iutInitialThetaOddModSupportFinset D,
        iutInitialThetaRepresentativeCoefficient D v = 1 := by
  rw [iutInitialThetaFullBaseQPilotLogSum_eq_coefficientWeightedPaperSum, paperSum_eq_sum]
  change (∑ v : iutInitialThetaOddModSupportFinset D,
      iutInitialThetaRepresentativeCoefficient D v * paperTerm D v) =
    (∑ v : iutInitialThetaOddModSupportFinset D, paperTerm D v) ↔ _
  constructor
  · intro h
    have hzero : (∑ v : iutInitialThetaOddModSupportFinset D,
        (1 - iutInitialThetaRepresentativeCoefficient D v) * paperTerm D v) = 0 := by
      simp_rw [sub_mul, one_mul]
      rw [Finset.sum_sub_distrib, h, sub_self]
    have hnonneg (v : iutInitialThetaOddModSupportFinset D) :
        0 ≤ (1 - iutInitialThetaRepresentativeCoefficient D v) * paperTerm D v :=
      mul_nonneg (sub_nonneg.mpr (iutInitialThetaRepresentativeCoefficient_mem_Ioc D v).2)
        (paperTerm_pos D v).le
    have hlocal := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hnonneg v)).mp hzero
    intro v
    have hz := (mul_eq_zero.mp (hlocal v (Finset.mem_univ _))).resolve_right
      (ne_of_gt (paperTerm_pos D v))
    linarith
  · intro h
    apply Finset.sum_congr rfl
    intro v hv
    rw [h v, one_mul]

end
end JoshiTeich.Act1Scene1
