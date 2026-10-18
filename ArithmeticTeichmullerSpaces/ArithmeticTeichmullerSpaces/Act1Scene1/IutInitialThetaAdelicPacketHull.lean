import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdelicPacketLogVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADELIC-PACKET-HULL
source: reference Concrete/Container, hull, and Cor312/ContainerHull,
hullFamily; Cor312/RightHandSide composes the region with its hull before
procession volume. Joshi III le:volume-lemma3 supplies the comparison pattern.
fidelity: replaces each actual finite component by its constructed least
principal normalization hull. At infinity keeps the existing radial shell,
which is already pi^|I| B_I. Proves compactness, positive finite local Haar,
common finite support, restricted-product containment and actual weighted
log-volume bounds. No paper locus, paper hull or final RHSData identity is
assumed or asserted. Original consumer proofs; no reference code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaAdelicPacketHull

open MeasureTheory IutInitialThetaAdelicPacketRegion
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) :
    Finite (IutInitialThetaFinitePacketRegion.Fiber D p) :=
  JoshiTeich.Prologue.Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) :
    Fintype (IutInitialThetaFinitePacketRegion.Fiber D p) := Fintype.ofFinite _

def region (j : ℕ) : (vQ : RationalPlace) → Set (Total D j vQ)
  | .finite p => IutInitialThetaFinitePacketHull.region D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.region D j

theorem source_subset_region (j : ℕ) (vQ : RationalPlace) :
    IutInitialThetaAdelicPacketRegion.region D j vQ ⊆ region D j vQ := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketHull.source_subset_region D p j
  | infinite => exact Set.Subset.rfl

theorem region_isCompact (j : ℕ) (vQ : RationalPlace) : IsCompact (region D j vQ) := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketHull.region_isCompact D p j
  | infinite => exact IutInitialThetaArchimedeanPacketRegion.region_isCompact D j

theorem packetMeasure_region_pos_lt_top (j : ℕ) (vQ : RationalPlace) :
    0 < packetMeasure D j vQ (region D j vQ) ∧
      packetMeasure D j vQ (region D j vQ) < ⊤ := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketHull.productMeasure_region_pos_lt_top D p j
  | infinite => exact IutInitialThetaArchimedeanPacketRegion.productMeasure_region_pos_lt_top D j

theorem region_eq_integralRegion_of_not_exceptional (j : ℕ) (vQ : RationalPlace)
    (hv : vQ ∉ exceptionalPlaces D) : region D j vQ = integralRegion D j vQ := by
  cases vQ with
  | finite p =>
    apply IutInitialThetaFinitePacketHull.region_eq_integralRegion_of_not_bad
    intro hp
    exact hv ((finite_mem_exceptionalPlaces D p).mpr
      ((IutInitialThetaFinitePacketLogVolume.mem_badPrimes D p).mpr hp))
  | infinite => exact False.elim (hv (Finset.mem_insert_self _ _))

theorem region_support_subset (j : ℕ) :
    {vQ | region D j vQ ≠ integralRegion D j vQ} ⊆ (exceptionalPlaces D : Set RationalPlace) := by
  intro vQ hv
  by_contra h
  exact hv (region_eq_integralRegion_of_not_exceptional D j vQ h)

theorem region_finite_support (j : ℕ) :
    {vQ | region D j vQ ≠ integralRegion D j vQ}.Finite :=
  (exceptionalPlaces D).finite_toSet.subset (region_support_subset D j)

theorem processionRegion_finite_support :
    {vQ | ∃ i : IutInitialThetaFinitePacketRegion.Index D,
      region D (i.val + 1) vQ ≠ integralRegion D (i.val + 1) vQ}.Finite := by
  apply (exceptionalPlaces D).finite_toSet.subset
  rintro vQ ⟨i, hi⟩
  exact region_support_subset D (i.val + 1) hi

def containerRegion (j : ℕ) : Set (Container D j) := {x | ∀ vQ, x vQ ∈ region D j vQ}

theorem source_containerRegion_subset (j : ℕ) :
    IutInitialThetaAdelicPacketRegion.containerRegion D j ⊆ containerRegion D j :=
  fun _ hx vQ => source_subset_region D j vQ (hx vQ)

theorem containerRegion_nonempty (j : ℕ) : (containerRegion D j).Nonempty :=
  (IutInitialThetaAdelicPacketRegion.containerRegion_nonempty D j).mono
    (source_containerRegion_subset D j)

theorem integral_eventually_of_mem_region (j : ℕ) (x : ∀ vQ, Total D j vQ)
    (hx : ∀ vQ, x vQ ∈ region D j vQ) :
    ∀ᶠ vQ in Filter.cofinite, x vQ ∈ integralRegion D j vQ := by
  filter_upwards [(exceptionalPlaces D).eventually_cofinite_notMem] with vQ hv
  rw [← region_eq_integralRegion_of_not_exceptional D j vQ hv]
  exact hx vQ

def toContainer (j : ℕ) (x : ∀ vQ, Total D j vQ) (hx : ∀ vQ, x vQ ∈ region D j vQ) :
    Container D j := ⟨x, integral_eventually_of_mem_region D j x hx⟩

theorem toContainer_mem (j : ℕ) (x : ∀ vQ, Total D j vQ)
    (hx : ∀ vQ, x vQ ∈ region D j vQ) : toContainer D j x hx ∈ containerRegion D j := hx

def packetLogVolume (j : ℕ) : RationalPlace → ℝ
  | .finite p => IutInitialThetaFinitePacketHull.packetLogVolume D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j

theorem finite_packetLogVolume_eq_productMeasure_log (p : Nat.Primes) (j : ℕ) :
    packetLogVolume D j (.finite p) =
      Real.log (packetMeasure D j (.finite p) (region D j (.finite p))).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  change IutInitialThetaFinitePacketHull.packetLogVolume D p j =
    Real.log (IutInitialThetaFinitePacketRegion.productMeasure D p j
      (IutInitialThetaFinitePacketHull.region D p j)).toReal / _
  calc
    _ = (∑ c : IutInitialThetaFinitePacketRegion.Tuple D p j,
        Real.log ((IutInitialThetaFinitePacketRegion.packet D p j c).normalizationHaar
          (IutInitialThetaFinitePacketHull.componentHull D p j c)).toReal) /
            (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
      simp only [IutInitialThetaFinitePacketHull.packetLogVolume,
        IutInitialThetaFinitePacketLogVolume.weighted_componentLogVolume, Finset.sum_div]
    _ = _ := by
      rw [IutInitialThetaFinitePacketHull.productMeasure_region, ENNReal.toReal_prod,
        Real.log_prod]
      intro c _
      exact (ENNReal.toReal_pos
        (IutInitialThetaFinitePacketHull.componentHull_haar_pos_lt_top D p j c).1.ne'
        (IutInitialThetaFinitePacketHull.componentHull_haar_pos_lt_top D p j c).2.ne).ne'

theorem source_packetLogVolume_le (j : ℕ) (vQ : RationalPlace) :
    IutInitialThetaAdelicPacketLogVolume.packetLogVolume D j vQ ≤ packetLogVolume D j vQ := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketHull.source_packetLogVolume_le D p j
  | infinite => exact le_refl _

theorem packetLogVolume_eq_zero_of_not_exceptional (j : ℕ) (vQ : RationalPlace)
    (hv : vQ ∉ exceptionalPlaces D) : packetLogVolume D j vQ = 0 := by
  cases vQ with
  | finite p =>
    apply IutInitialThetaFinitePacketHull.packetLogVolume_eq_zero_of_not_bad
    intro hp
    exact hv ((finite_mem_exceptionalPlaces D p).mpr
      ((IutInitialThetaFinitePacketLogVolume.mem_badPrimes D p).mpr hp))
  | infinite => exact False.elim (hv (Finset.mem_insert_self _ _))

theorem packetLogVolume_support_subset (j : ℕ) :
    Function.support (packetLogVolume D j) ⊆ (exceptionalPlaces D : Set RationalPlace) := by
  intro vQ hv
  by_contra h
  exact hv (packetLogVolume_eq_zero_of_not_exceptional D j vQ h)

theorem packetLogVolume_finite_support (j : ℕ) :
    (Function.support (packetLogVolume D j)).Finite :=
  (exceptionalPlaces D).finite_toSet.subset (packetLogVolume_support_subset D j)

def globalLogVolume (j : ℕ) : ℝ := ∑ᶠ vQ, packetLogVolume D j vQ

theorem globalLogVolume_eq_sum (j : ℕ) :
    globalLogVolume D j = ∑ vQ ∈ exceptionalPlaces D, packetLogVolume D j vQ :=
  finsum_eq_sum_of_support_subset _ (packetLogVolume_support_subset D j)

theorem source_globalLogVolume_le (j : ℕ) :
    IutInitialThetaAdelicPacketLogVolume.globalLogVolume D j ≤ globalLogVolume D j := by
  rw [globalLogVolume_eq_sum, IutInitialThetaAdelicPacketLogVolume.globalLogVolume_eq_sum]
  exact Finset.sum_le_sum fun vQ _ => source_packetLogVolume_le D j vQ

theorem globalLogVolume_eq_finite_add_arch (j : ℕ) :
    globalLogVolume D j =
      (∑ p ∈ IutInitialThetaFinitePacketLogVolume.badPrimes D,
        IutInitialThetaFinitePacketHull.packetLogVolume D p j) +
          IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  rw [globalLogVolume_eq_sum, exceptionalPlaces, Finset.sum_insert (by simp), Finset.sum_image]
  · exact add_comm _ _
  · intro p _ q _ h
    exact RationalPlace.finite.inj h

theorem globalLogVolume_bounds (j : ℕ) :
    IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j -
        ((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤ globalLogVolume D j ∧
      globalLogVolume D j ≤ IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  constructor
  · exact (IutInitialThetaAdelicPacketLogVolume.globalLogVolume_bounds D j).1.trans
      (source_globalLogVolume_le D j)
  · rw [globalLogVolume_eq_finite_add_arch]
    have h := Finset.sum_nonpos (s := IutInitialThetaFinitePacketLogVolume.badPrimes D)
      (fun p _ => IutInitialThetaFinitePacketHull.packetLogVolume_nonpos D p j)
    simpa only [zero_add] using add_le_add h
      (le_refl (IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j))

def processionLogVolume : ℝ :=
  (∑ i : IutInitialThetaFinitePacketRegion.Index D, globalLogVolume D (i.val + 1)) /
    (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ)

theorem source_processionLogVolume_le :
    IutInitialThetaAdelicPacketLogVolume.processionLogVolume D ≤ processionLogVolume D := by
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => source_globalLogVolume_le D (i.val + 1)) (Nat.cast_nonneg _)

theorem processionLogVolume_bounds :
    IutInitialThetaArchimedeanPacketRegion.processionLogVolume D -
        IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
          JoshiTeich.ReferenceIut.QPilotData.absLogQ
            (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤ processionLogVolume D ∧
      processionLogVolume D ≤ IutInitialThetaArchimedeanPacketRegion.processionLogVolume D := by
  constructor
  · exact (IutInitialThetaAdelicPacketLogVolume.processionLogVolume_bounds D).1.trans
      (source_processionLogVolume_le D)
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun i _ => (globalLogVolume_bounds D (i.val + 1)).2) (Nat.cast_nonneg _)

end
end JoshiTeich.Act1Scene1.IutInitialThetaAdelicPacketHull
