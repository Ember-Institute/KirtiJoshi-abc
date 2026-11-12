import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdelicWitnessHullBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperRootNormProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITNESS-HULL-HAAR-PRODUCT
source: Joshi III ss:weighted-vol, le:volume-lemma3 and multiplicative
adelic volumes in th:moccor-Mochizuki-form2; reference LogVolume's separate
component / packet / procession normalizations.
fidelity: actual finite products of positive normalized packet Haar,
with the proved global-degree exponents and a separate procession root.
Their logs equal the existing adelic log-volume minus the explicit actual
infinite contribution. The selected paper-root product enters only through
the proved strict q-accounting inequality, with squareAverage retained.
Original proofs; no reference source code copied.
boundary: Scene1/Derived; no paper thetaVolume or final 3.12 identity.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaWitnessHullHaarProduct

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open IutInitialThetaAdelicWitnessHullBound
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-- Dimension-normalized actual product Haar at one finite rational place. -/
def packetVolume (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) : ℝ :=
  (IutInitialThetaAdelicPacketRegion.packetMeasure D j (.finite p)
    (IutInitialThetaAdelicHullClosure.productRegion D j (.finite p)
      (hullFamily D j U (.finite p)))).toReal ^
        (1 / (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1))

theorem packetVolume_eq_exp (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) :
    packetVolume D j U p = Real.exp
      (IutInitialThetaAdelicFamilyLogVolume.packetLogVolume D j (.finite p)
        (hullFamily D j U (.finite p))) := by
  have hm := IutInitialThetaAdelicFamilyLogVolume.packetMeasure_productRegion_pos_lt_top
    D j (.finite p) (hullFamily D j U (.finite p))
  rw [packetVolume, Real.rpow_def_of_pos (ENNReal.toReal_pos hm.1.ne' hm.2.ne)]
  unfold IutInitialThetaAdelicFamilyLogVolume.packetLogVolume
  congr 1
  ring

theorem packetVolume_pos (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) :
    0 < packetVolume D j U p := by
  rw [packetVolume_eq_exp]
  exact Real.exp_pos _

theorem packetVolume_le_one (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) :
    packetVolume D j U p ≤ 1 := by
  rw [packetVolume_eq_exp, Real.exp_le_one_iff]
  exact packetLogVolume_nonpos D p j U

theorem packetVolume_eq_one_of_not_bad (j : ℕ) (U : RawFamily D j) (p : Nat.Primes)
    (hp : p ∉ IutInitialThetaFinitePacketLogVolume.badPrimes D) : packetVolume D j U p = 1 := by
  have he := hullFamily_support_subset D j U
  have hne : RationalPlace.finite p ∉ IutInitialThetaAdelicPacketRegion.exceptionalPlaces D :=
    fun h => hp ((IutInitialThetaAdelicPacketRegion.finite_mem_exceptionalPlaces D p).mp h)
  have hi : hullFamily D j U (.finite p) =
      IutInitialThetaAdelicHullClosure.integralFamily D j (.finite p) := by
    by_contra h
    exact hne (he h)
  rw [packetVolume_eq_exp, hi, IutInitialThetaAdelicFamilyLogVolume.packetLogVolume_integral,
    Real.exp_zero]

/-- A finite product, relative to the integral baseline, over the actual common bad set. -/
def finiteVolume (j : ℕ) (U : RawFamily D j) : ℝ :=
  ∏ p ∈ IutInitialThetaFinitePacketLogVolume.badPrimes D, packetVolume D j U p

theorem finiteVolume_pos (j : ℕ) (U : RawFamily D j) : 0 < finiteVolume D j U :=
  Finset.prod_pos fun p _ => packetVolume_pos D j U p

theorem finiteVolume_le_one (j : ℕ) (U : RawFamily D j) : finiteVolume D j U ≤ 1 :=
  Finset.prod_le_one (fun p _ => (packetVolume_pos D j U p).le)
    (fun p _ => packetVolume_le_one D j U p)

theorem finiteVolume_eq_exp (j : ℕ) (U : RawFamily D j) :
    finiteVolume D j U = Real.exp
      (IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U) -
        IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j) := by
  rw [finiteVolume, globalLogVolume_eq_finite_add_arch, add_sub_cancel_right, Real.exp_sum]
  exact Finset.prod_congr rfl fun p _ => packetVolume_eq_exp D j U p

theorem log_finiteVolume (j : ℕ) (U : RawFamily D j) :
    Real.log (finiteVolume D j U) =
      IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U) -
        IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  rw [finiteVolume_eq_exp, Real.log_exp]

/-- Restores the infinite-place contribution explicitly. -/
theorem adelic_exp_eq_finite_mul_arch (j : ℕ) (U : RawFamily D j) :
    Real.exp (IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U)) =
      finiteVolume D j U * Real.exp (IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j) := by
  rw [finiteVolume_eq_exp, ← Real.exp_add, sub_add_cancel]

theorem finiteVolume_lower_bound (j : ℕ) (U : RawFamily D j) :
    Real.exp (-((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
      (IutTorsionQRootSource.iutInitialThetaQPilotData D)) ≤ finiteVolume D j U := by
  rw [finiteVolume_eq_exp, Real.exp_le_exp]
  have hb := (globalLogVolume_bounds D j U).1
  linarith

theorem singleton_finiteVolume_eq (j : ℕ) :
    finiteVolume D j (singletonFamily D j) =
      Real.exp (-((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D)) := by
  rw [finiteVolume_eq_exp, singleton_globalLogVolume_eq]
  congr 1
  ring

/-- The procession average in log coordinates is a separate geometric mean. -/
def finiteProcessionVolume (U : ∀ i : Index D, RawFamily D (i.val + 1)) : ℝ :=
  (∏ i : Index D, finiteVolume D (i.val + 1) (U i)) ^
    (1 / (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ))

theorem finiteProcessionVolume_eq_exp (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    finiteProcessionVolume D U = Real.exp (processionLogVolume D U -
      IutInitialThetaArchimedeanPacketRegion.processionLogVolume D) := by
  rw [finiteProcessionVolume, Real.rpow_def_of_pos (Finset.prod_pos
    (fun i _ => finiteVolume_pos D (i.val + 1) (U i))), Real.log_prod
      (fun i _ => (finiteVolume_pos D (i.val + 1) (U i)).ne')]
  simp only [log_finiteVolume, Finset.sum_sub_distrib, processionLogVolume,
    IutInitialThetaAdelicFamilyLogVolume.processionLogVolume,
    IutInitialThetaArchimedeanPacketRegion.processionLogVolume]
  congr 1
  ring

theorem finiteProcessionVolume_pos (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    0 < finiteProcessionVolume D U := by
  rw [finiteProcessionVolume_eq_exp]
  exact Real.exp_pos _

theorem finiteProcessionVolume_le_one (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    finiteProcessionVolume D U ≤ 1 := by
  rw [finiteProcessionVolume_eq_exp, Real.exp_le_one_iff]
  exact sub_nonpos.mpr (processionLogVolume_bounds D U).2

theorem log_finiteProcessionVolume (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    Real.log (finiteProcessionVolume D U) = processionLogVolume D U -
      IutInitialThetaArchimedeanPacketRegion.processionLogVolume D := by
  rw [finiteProcessionVolume_eq_exp, Real.log_exp]

theorem adelicProcession_exp_eq_finite_mul_arch (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    Real.exp (processionLogVolume D U) = finiteProcessionVolume D U *
      Real.exp (IutInitialThetaArchimedeanPacketRegion.processionLogVolume D) := by
  rw [finiteProcessionVolume_eq_exp, ← Real.exp_add, sub_add_cancel]

theorem finiteProcessionVolume_lower_bound (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    Real.exp (-(IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D))) ≤
        finiteProcessionVolume D U := by
  rw [finiteProcessionVolume_eq_exp, Real.exp_le_exp]
  have hb := (processionLogVolume_bounds D U).1
  linarith

theorem singleton_finiteProcessionVolume_eq :
    finiteProcessionVolume D (fun i => singletonFamily D (i.val + 1)) =
      Real.exp (-(IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D))) := by
  rw [finiteProcessionVolume_eq_exp, singleton_processionLogVolume_eq]
  congr 1
  ring

theorem singleton_finiteProcessionVolume_eq_exp_neg_coefficientWeightedPaperSum :
    finiteProcessionVolume D (fun i => singletonFamily D (i.val + 1)) =
      Real.exp (-(IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
        (∑ v : iutInitialThetaVBadModuliFinset D,
          iutInitialThetaRepresentativeCoefficient D
              (iutInitialThetaVBadModuliAt D v) *
            VBadSelectedPaper.paperTerm D v))) := by
  rw [singleton_finiteProcessionVolume_eq,
    VBadSelectedPaper.referenceAbsLogQ_eq_coefficientWeightedPaperSum]

theorem singleton_adelicProcession_exp_eq_weightedPaper_mul_arch :
    Real.exp (processionLogVolume D
      (fun i => singletonFamily D (i.val + 1))) =
      Real.exp (-(IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
        (∑ v : iutInitialThetaVBadModuliFinset D,
          iutInitialThetaRepresentativeCoefficient D
              (iutInitialThetaVBadModuliAt D v) *
            VBadSelectedPaper.paperTerm D v))) *
        Real.exp (IutInitialThetaArchimedeanPacketRegion.processionLogVolume D) := by
  rw [adelicProcession_exp_eq_finite_mul_arch,
    singleton_finiteProcessionVolume_eq_exp_neg_coefficientWeightedPaperSum]

/-- The known strict q-accounting gap gives a bound, not a weight identity. -/
theorem selectedPaperRootProduct_pow_lt_finiteProcessionVolume
    (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    actualSelectedPaperRootNormProduct D ^ IutInitialThetaFiniteGlobalLowerBound.squareAverage D <
      finiteProcessionVolume D U := by
  have hp := (actualSelectedPaperRootNormProduct_mem_Ioo D).1
  rw [Real.rpow_def_of_pos hp]
  apply lt_of_lt_of_le _ (finiteProcessionVolume_lower_bound D U)
  apply Real.exp_lt_exp.mpr
  have hq := iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum D
  rw [← actualSelectedPaperRootNormProduct_negLog_eq_paperSum D] at hq
  have hs := IutInitialThetaFiniteGlobalLowerBound.squareAverage_pos D
  nlinarith

theorem neg_abs_log_finiteProcessionVolume (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    -|Real.log (finiteProcessionVolume D U)| = Real.log (finiteProcessionVolume D U) := by
  rw [abs_of_nonpos (Real.log_nonpos (finiteProcessionVolume_pos D U).le
    (finiteProcessionVolume_le_one D U)), neg_neg]

theorem finiteProcessionCost_lt_weightedPaperSum (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    -Real.log (finiteProcessionVolume D U) < IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
      iutInitialThetaSelectedQRootPaperSum D := by
  have h := Real.log_lt_log
    (Real.rpow_pos_of_pos (actualSelectedPaperRootNormProduct_mem_Ioo D).1 _)
    (selectedPaperRootProduct_pow_lt_finiteProcessionVolume D U)
  rw [Real.log_rpow (actualSelectedPaperRootNormProduct_mem_Ioo D).1] at h
  rw [← actualSelectedPaperRootNormProduct_negLog_eq_paperSum D]
  nlinarith

theorem finiteProcessionCost_le_coefficientWeightedPaperSum
    (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    -Real.log (finiteProcessionVolume D U) ≤
      IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
        (∑ v : iutInitialThetaVBadModuliFinset D,
          iutInitialThetaRepresentativeCoefficient D
              (iutInitialThetaVBadModuliAt D v) *
            VBadSelectedPaper.paperTerm D v) := by
  have hlog := Real.log_le_log
    (Real.exp_pos
      (-(IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D))))
    (finiteProcessionVolume_lower_bound D U)
  rw [Real.log_exp] at hlog
  rw [← VBadSelectedPaper.referenceAbsLogQ_eq_coefficientWeightedPaperSum D]
  nlinarith

theorem finiteProcessionVolume_ge_exp_neg_coefficientWeightedPaperSum
    (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    Real.exp (-(IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
      (∑ v : iutInitialThetaVBadModuliFinset D,
        iutInitialThetaRepresentativeCoefficient D
            (iutInitialThetaVBadModuliAt D v) *
          VBadSelectedPaper.paperTerm D v))) ≤
      finiteProcessionVolume D U := by
  rw [← VBadSelectedPaper.referenceAbsLogQ_eq_coefficientWeightedPaperSum D]
  exact finiteProcessionVolume_lower_bound D U

theorem pointOrbit_finiteProcessionVolume_eq :
    finiteProcessionVolume D (fun i => pointOrbitFamily D (i.val + 1)) =
      Real.exp (IutInitialThetaAdelicPacketHull.processionLogVolume D -
        IutInitialThetaArchimedeanPacketRegion.processionLogVolume D) := by
  rw [finiteProcessionVolume_eq_exp, pointOrbit_processionLogVolume_eq_existing]

theorem sourceRegion_finiteProcessionVolume_eq :
    finiteProcessionVolume D (fun i => sourceRegionFamily D (i.val + 1)) =
      Real.exp (IutInitialThetaAdelicPacketHull.processionLogVolume D -
        IutInitialThetaArchimedeanPacketRegion.processionLogVolume D) := by
  rw [finiteProcessionVolume_eq_exp, sourceRegion_processionLogVolume_eq_existing]

end
end JoshiTeich.Act1Scene1.IutInitialThetaWitnessHullHaarProduct
