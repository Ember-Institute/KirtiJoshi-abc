import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdelicHullClosure
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaArchimedeanPacketLogVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketPrimeLogVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADELIC-FAMILY-LOG-VOLUME
source: reference Cor312/LogVolume, packetVol_product, finite_support_packetVol,
globalVol and processionVol; ContainerHull, hullFamily; Joshi III ss:weighted-vol.
fidelity: actual bounded positive-Haar component families over the same D.
The packet functional is actual product-Haar log divided by [Kt:Q]^(j+1),
with proved finite/infinite weighted combination laws. Global comparison
uses actual finite support; closure and source/hull/shell are consumers.
Original proofs; no reference source code copied.
boundary: Scene1/Derived; no paper weights or thetaVolume identification.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaAdelicFamilyLogVolume

open NumberField MeasureTheory IutInitialThetaAdelicPacketRegion IutInitialThetaAdelicHullClosure
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) :
    Finite (IutInitialThetaFinitePacketRegion.Fiber D p) := Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) :
    Fintype (IutInitialThetaFinitePacketRegion.Fiber D p) := Fintype.ofFinite _

theorem packetMeasure_productRegion_pos_lt_top (j : ℕ) (vQ : RationalPlace)
    (U : PacketFamily D j vQ) :
    0 < packetMeasure D j vQ (productRegion D j vQ U) ∧
      packetMeasure D j vQ (productRegion D j vQ U) < ⊤ := by
  cases vQ with
  | finite p =>
    have hprod : packetMeasure D j (.finite p) (productRegion D j (.finite p) U) =
        ∏ c : IutInitialThetaFinitePacketRegion.Tuple D p j,
          (IutInitialThetaFinitePacketRegion.packet D p j c).normalizationHaar (U c).1 :=
      Measure.pi_pi _ _
    rw [hprod]
    exact ⟨bot_lt_iff_ne_bot.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => (U c).2.2.ne'),
      ENNReal.prod_lt_top fun c _ => (U c).2.1.measure_lt_top⟩
  | infinite =>
    have hprod : packetMeasure D j .infinite (productRegion D j .infinite U) =
        ∏ c : IutInitialThetaArchimedeanPacketRegion.Tuple D j,
          LocalArchimedean.normalizedHaar c (U c).1 := Measure.pi_pi _ _
    rw [hprod]
    exact ⟨bot_lt_iff_ne_bot.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => (U c).2.2.ne'),
      ENNReal.prod_lt_top fun c _ => (U c).2.1.measure_lt_top⟩


theorem productRegion_nonempty (j : ℕ) (vQ : RationalPlace) (U : PacketFamily D j vQ) :
    (productRegion D j vQ U).Nonempty := by
  by_contra h
  have hpos := (packetMeasure_productRegion_pos_lt_top D j vQ U).1
  rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty] at hpos
  exact (lt_irrefl _ hpos)

def packetLogVolume (j : ℕ) (vQ : RationalPlace) (U : PacketFamily D j vQ) : ℝ :=
  Real.log (packetMeasure D j vQ (productRegion D j vQ U)).toReal /
    (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1)

theorem finite_packetLogVolume_eq_weighted (j : ℕ) (p : Nat.Primes)
    (U : PacketFamily D j (.finite p)) :
    packetLogVolume D j (.finite p) U =
      ∑ c : IutInitialThetaFinitePacketRegion.Tuple D p j,
        IutInitialThetaFinitePacketLogVolume.tupleWeight D p j c *
          IutInitialThetaFinitePacketLogVolume.componentLogVolume D p j c (U c).1 :=
  (IutInitialThetaFinitePacketPrimeLogVolume.familyLogVolume_eq_productMeasure_log D p j _
    (fun c => (U c).2.2) (fun c => (U c).2.1.measure_lt_top)).symm

theorem infinite_packetLogVolume_eq_weighted (j : ℕ) (U : PacketFamily D j .infinite) :
    packetLogVolume D j .infinite U =
      ∑ c : IutInitialThetaArchimedeanPacketRegion.Tuple D j,
        IutInitialThetaArchimedeanPacketRegion.tupleWeight D j c *
          LocalArchimedean.normalizationLogVolume c (U c).1 :=
  (IutInitialThetaArchimedeanPacketLogVolume.familyLogVolume_eq_productMeasure_log D j _
    (fun c => (U c).2.2) (fun c => (U c).2.1.measure_lt_top)).symm

theorem packetLogVolume_integral (j : ℕ) (vQ : RationalPlace) :
    packetLogVolume D j vQ (integralFamily D j vQ) = 0 := by
  rw [packetLogVolume, productRegion_integralFamily, packetMeasure_integralRegion]
  simp only [ENNReal.toReal_one, Real.log_one, zero_div]

theorem packetLogVolume_mono (j : ℕ) (vQ : RationalPlace) {U V : PacketFamily D j vQ}
    (hUV : U ≤ V) : packetLogVolume D j vQ U ≤ packetLogVolume D j vQ V := by
  unfold packetLogVolume
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
  apply Real.log_le_log
  · exact ENNReal.toReal_pos (packetMeasure_productRegion_pos_lt_top D j vQ U).1.ne'
      (packetMeasure_productRegion_pos_lt_top D j vQ U).2.ne
  · exact ENNReal.toReal_mono (packetMeasure_productRegion_pos_lt_top D j vQ V).2.ne
      (measure_mono (productRegion_mono D j vQ hUV))

/-- Genuine finite support relative to the integral component family. -/
abbrev AdmissibleFamily (j : ℕ) :=
  {U : Family D j // {vQ | U vQ ≠ integralFamily D j vQ}.Finite}

def integralAdmissibleFamily (j : ℕ) : AdmissibleFamily D j :=
  ⟨integralFamily D j, by simp⟩

def closureFamily (j : ℕ) (U : AdmissibleFamily D j) : AdmissibleFamily D j :=
  ⟨adelicClosure D j U.1, family_finite_support_closure D j U.1 U.2⟩

theorem packetLogVolume_support_subset (j : ℕ) (U : AdmissibleFamily D j) :
    Function.support (fun vQ => packetLogVolume D j vQ (U.1 vQ)) ⊆
      {vQ | U.1 vQ ≠ integralFamily D j vQ} := by
  intro vQ hv heq
  apply hv
  change packetLogVolume D j vQ (U.1 vQ) = 0
  rw [heq, packetLogVolume_integral]

theorem packetLogVolume_finite_support (j : ℕ) (U : AdmissibleFamily D j) :
    (Function.support fun vQ => packetLogVolume D j vQ (U.1 vQ)).Finite :=
  U.2.subset (packetLogVolume_support_subset D j U)

def globalLogVolume (j : ℕ) (U : AdmissibleFamily D j) : ℝ :=
  ∑ᶠ vQ, packetLogVolume D j vQ (U.1 vQ)

theorem globalLogVolume_eq_sum (j : ℕ) (U : AdmissibleFamily D j) :
    globalLogVolume D j U =
      ∑ vQ ∈ U.2.toFinset, packetLogVolume D j vQ (U.1 vQ) := by
  apply finsum_eq_sum_of_support_subset
  intro vQ hv
  exact U.2.mem_toFinset.mpr (packetLogVolume_support_subset D j U hv)

theorem globalLogVolume_mono (j : ℕ) {U V : AdmissibleFamily D j} (hUV : U.1 ≤ V.1) :
    globalLogVolume D j U ≤ globalLogVolume D j V :=
  finsum_le_finsum (packetLogVolume_finite_support D j U) (packetLogVolume_finite_support D j V)
    (fun vQ => packetLogVolume_mono D j vQ (hUV vQ))

theorem globalLogVolume_integral (j : ℕ) :
    globalLogVolume D j (integralAdmissibleFamily D j) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro vQ
  exact packetLogVolume_integral D j vQ

theorem globalLogVolume_le_closure (j : ℕ) (U : AdmissibleFamily D j) :
    globalLogVolume D j U ≤ globalLogVolume D j (closureFamily D j U) :=
  globalLogVolume_mono D j ((adelicClosure D j).le_closure U.1)

theorem globalLogVolume_closure_idem (j : ℕ) (U : AdmissibleFamily D j) :
    globalLogVolume D j (closureFamily D j (closureFamily D j U)) =
      globalLogVolume D j (closureFamily D j U) := by
  have he : closureFamily D j (closureFamily D j U) = closureFamily D j U :=
    Subtype.ext ((adelicClosure D j).idempotent U.1)
  rw [he]

def sourceAdmissibleFamily (j : ℕ) : AdmissibleFamily D j :=
  ⟨sourceFamily D j, sourceFamily_finite_support D j⟩

theorem shellFamily_finite_support (j : ℕ) :
    {vQ | shellFamily D j vQ ≠ integralFamily D j vQ}.Finite := by
  apply (IutInitialThetaAdelicLogShell.exceptionalPlaces D).finite_toSet.subset
  intro vQ hv
  by_contra he
  apply hv
  cases vQ with
  | infinite => exact False.elim (he (Finset.mem_insert_self _ _))
  | finite p =>
    funext c
    apply Subtype.ext
    have hprod := IutInitialThetaAdelicLogShell.region_eq_integralRegion_of_not_exceptional D j (.finite p) he
    have hpi := Set.pi_subset_pi_iff.mp hprod.subset
    rcases hpi with h | h
    · apply Set.Subset.antisymm (h c (Set.mem_univ c))
      exact (IutInitialThetaFinitePacketRegion.packet D p j c).normalization_subset_saturatedLogShell
    · exact False.elim ((productRegion_nonempty D j (.finite p) (shellFamily D j (.finite p))).ne_empty h)

def shellAdmissibleFamily (j : ℕ) : AdmissibleFamily D j :=
  ⟨shellFamily D j, shellFamily_finite_support D j⟩


theorem globalLogVolume_closure_le_shell (j : ℕ) (U : AdmissibleFamily D j)
    (hU : U.1 ≤ shellFamily D j) :
    globalLogVolume D j (closureFamily D j U) ≤ globalLogVolume D j (shellAdmissibleFamily D j) := by
  apply globalLogVolume_mono
  change adelicClosure D j U.1 ≤ shellFamily D j
  rw [← adelicClosure_shellFamily D j]
  exact (adelicClosure D j).monotone hU

theorem packetLogVolume_source (j : ℕ) (vQ : RationalPlace) :
    packetLogVolume D j vQ (sourceFamily D j vQ) =
      IutInitialThetaAdelicPacketLogVolume.packetLogVolume D j vQ := by
  unfold packetLogVolume
  rw [productRegion_sourceFamily]
  cases vQ with
  | finite p => exact (IutInitialThetaFinitePacketLogVolume.packetLogVolume_eq_productMeasure_log D p j).symm
  | infinite => exact (IutInitialThetaArchimedeanPacketLogVolume.packetLogVolume_eq_productMeasure_log D j).symm

theorem packetLogVolume_hull (j : ℕ) (vQ : RationalPlace) :
    packetLogVolume D j vQ (adelicClosure D j (sourceFamily D j) vQ) =
      IutInitialThetaAdelicPacketHull.packetLogVolume D j vQ := by
  unfold packetLogVolume
  rw [productRegion_closure_sourceFamily]
  cases vQ with
  | finite p => exact (IutInitialThetaAdelicPacketHull.finite_packetLogVolume_eq_productMeasure_log D p j).symm
  | infinite => exact (IutInitialThetaArchimedeanPacketLogVolume.packetLogVolume_eq_productMeasure_log D j).symm

theorem packetLogVolume_shell (j : ℕ) (vQ : RationalPlace) :
    packetLogVolume D j vQ (shellFamily D j vQ) =
      IutInitialThetaAdelicLogShell.packetLogVolume D j vQ := by
  unfold packetLogVolume
  rw [productRegion_shellFamily]
  cases vQ with
  | finite p => exact (IutInitialThetaFinitePacketLogShell.packetLogVolume_eq_productMeasure_log D p j).symm
  | infinite => exact (IutInitialThetaArchimedeanPacketLogVolume.packetLogVolume_eq_productMeasure_log D j).symm

theorem globalLogVolume_source (j : ℕ) :
    globalLogVolume D j (sourceAdmissibleFamily D j) =
      IutInitialThetaAdelicPacketLogVolume.globalLogVolume D j := by
  unfold globalLogVolume IutInitialThetaAdelicPacketLogVolume.globalLogVolume
  congr 1
  funext vQ
  exact packetLogVolume_source D j vQ

theorem globalLogVolume_hull (j : ℕ) :
    globalLogVolume D j (closureFamily D j (sourceAdmissibleFamily D j)) =
      IutInitialThetaAdelicPacketHull.globalLogVolume D j := by
  unfold globalLogVolume IutInitialThetaAdelicPacketHull.globalLogVolume
  congr 1
  funext vQ
  exact packetLogVolume_hull D j vQ

theorem globalLogVolume_shell (j : ℕ) :
    globalLogVolume D j (shellAdmissibleFamily D j) =
      IutInitialThetaAdelicLogShell.globalLogVolume D j := by
  unfold globalLogVolume IutInitialThetaAdelicLogShell.globalLogVolume
  congr 1
  funext vQ
  exact packetLogVolume_shell D j vQ

/-- The separate, unweighted average over the actual standard procession. -/
def processionLogVolume
    (U : ∀ i : IutInitialThetaFinitePacketRegion.Index D, AdmissibleFamily D (i.val + 1)) : ℝ :=
  (∑ i, globalLogVolume D (i.val + 1) (U i)) / (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ)

theorem processionLogVolume_mono
    {U V : ∀ i : IutInitialThetaFinitePacketRegion.Index D, AdmissibleFamily D (i.val + 1)}
    (hUV : ∀ i, (U i).1 ≤ (V i).1) :
    processionLogVolume D U ≤ processionLogVolume D V :=
  div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => globalLogVolume_mono D (i.val + 1) (hUV i)) (Nat.cast_nonneg _)


theorem processionLogVolume_integral :
    processionLogVolume D (fun i => integralAdmissibleFamily D (i.val + 1)) = 0 := by
  simp only [processionLogVolume, globalLogVolume_integral, Finset.sum_const_zero, zero_div]

theorem processionLogVolume_le_closure
    (U : ∀ i : IutInitialThetaFinitePacketRegion.Index D, AdmissibleFamily D (i.val + 1)) :
    processionLogVolume D U ≤
      processionLogVolume D (fun i => closureFamily D (i.val + 1) (U i)) :=
  processionLogVolume_mono D (fun i => (adelicClosure D (i.val + 1)).le_closure (U i).1)

theorem processionLogVolume_closure_idem
    (U : ∀ i : IutInitialThetaFinitePacketRegion.Index D, AdmissibleFamily D (i.val + 1)) :
    processionLogVolume D (fun i => closureFamily D (i.val + 1) (closureFamily D (i.val + 1) (U i))) =
      processionLogVolume D (fun i => closureFamily D (i.val + 1) (U i)) := by
  simp only [processionLogVolume, globalLogVolume_closure_idem]

theorem processionLogVolume_closure_le_shell
    (U : ∀ i : IutInitialThetaFinitePacketRegion.Index D, AdmissibleFamily D (i.val + 1))
    (hU : ∀ i, (U i).1 ≤ shellFamily D (i.val + 1)) :
    processionLogVolume D (fun i => closureFamily D (i.val + 1) (U i)) ≤
      processionLogVolume D (fun i => shellAdmissibleFamily D (i.val + 1)) :=
  div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => globalLogVolume_closure_le_shell D (i.val + 1) (U i) (hU i))
    (Nat.cast_nonneg _)

theorem processionLogVolume_source :
    processionLogVolume D (fun i => sourceAdmissibleFamily D (i.val + 1)) =
      IutInitialThetaAdelicPacketLogVolume.processionLogVolume D := by
  simp only [processionLogVolume, globalLogVolume_source,
    IutInitialThetaAdelicPacketLogVolume.processionLogVolume]

theorem processionLogVolume_hull :
    processionLogVolume D (fun i => closureFamily D (i.val + 1) (sourceAdmissibleFamily D (i.val + 1))) =
      IutInitialThetaAdelicPacketHull.processionLogVolume D := by
  simp only [processionLogVolume, globalLogVolume_hull, IutInitialThetaAdelicPacketHull.processionLogVolume]

theorem processionLogVolume_shell :
    processionLogVolume D (fun i => shellAdmissibleFamily D (i.val + 1)) =
      IutInitialThetaAdelicLogShell.processionLogVolume D := by
  simp only [processionLogVolume, globalLogVolume_shell, IutInitialThetaAdelicLogShell.processionLogVolume]

end
end JoshiTeich.Act1Scene1.IutInitialThetaAdelicFamilyLogVolume
