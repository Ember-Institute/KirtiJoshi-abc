import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorUnramifiedLogShell
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketLogShell
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdelicPacketHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADELIC-LOG-SHELL
source: reference Concrete/Container, logShell_finiteSupport and
logShellAdmissible; LocalConstruct/LogShell unramified equality;
Joshi III tensor log-shell construction and finite adelic support.
fidelity: on the actual common D/tuple/rational-place carrier, constructs the
finite saturated ordinary shells and the infinite radial shell. The common
exceptional set is infinity, 2 and actual torsion-field ramified primes.
Proves integral equality off it, procession-wide finite support, and actual
restricted-product containment. Global/procession shell logs are honest
finite sums, nonnegative, and dominate the constructed source/hull logs.
No paper BK/theta-volume or final RHSData identity is asserted.
Original consumer proofs; no reference code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaAdelicLogShell

open NumberField MeasureTheory IutInitialThetaAdelicPacketRegion
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

def ramifiedPrimes : Finset Nat.Primes :=
  (LocalCompletion.ramified_finite (K := ↥D.prime.torsionField)).toFinset.image
    (fun w => ⟨Arithmetic.residueChar w, Arithmetic.residueChar_prime w⟩)

theorem ramIdx_eq_one_of_not_ramifiedPrimes (p : Nat.Primes)
    (hp : p ∉ ramifiedPrimes D) (w : FinitePlace ↥D.prime.torsionField)
    (hw : Arithmetic.residueChar w = (p : ℕ)) : Arithmetic.ramIdx w = 1 := by
  by_contra he
  apply hp
  apply Finset.mem_image.mpr
  exact ⟨w, (LocalCompletion.ramified_finite (K := ↥D.prime.torsionField)).mem_toFinset.mpr he,
    Subtype.ext hw⟩

def exceptionalPlaces : Finset RationalPlace :=
  insert .infinite (insert (.finite ⟨2, Nat.prime_two⟩) ((ramifiedPrimes D).image .finite))

def region (j : ℕ) : (vQ : RationalPlace) → Set (Total D j vQ)
  | .finite p => IutInitialThetaFinitePacketLogShell.region D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.region D j

theorem finite_region_eq_integral_of_unramified (p : Nat.Primes) (j : ℕ)
    (hodd : Odd (p : ℕ)) (hp : p ∉ ramifiedPrimes D) :
    region D j (.finite p) = integralRegion D j (.finite p) := by
  change Set.pi Set.univ (IutInitialThetaFinitePacketLogShell.componentShell D p j) =
    Set.pi Set.univ _
  congr 1
  funext c
  exact (IutInitialThetaFinitePacketRegion.packet D p j c).saturatedLogShell_eq_normalization_of_unramified hodd
      (fun i => ramIdx_eq_one_of_not_ramifiedPrimes D p hp (c i).1 (c i).2)

theorem region_eq_integralRegion_of_not_exceptional (j : ℕ) (vQ : RationalPlace)
    (hv : vQ ∉ exceptionalPlaces D) : region D j vQ = integralRegion D j vQ := by
  cases vQ with
  | infinite => exact False.elim (hv (Finset.mem_insert_self _ _))
  | finite p =>
    have hp2 : (p : ℕ) ≠ 2 := by
      intro h
      apply hv
      apply Finset.mem_insert_of_mem
      exact Finset.mem_insert.mpr (Or.inl (congrArg RationalPlace.finite (Subtype.ext h)))
    have hpr : p ∉ ramifiedPrimes D := by
      intro h
      exact hv (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, h, rfl⟩)))
    exact finite_region_eq_integral_of_unramified D p j
      (p.property.eq_two_or_odd'.resolve_left hp2) hpr

theorem region_isCompact (j : ℕ) (vQ : RationalPlace) : IsCompact (region D j vQ) := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketLogShell.region_isCompact D p j
  | infinite => exact IutInitialThetaArchimedeanPacketRegion.region_isCompact D j

theorem packetMeasure_region_pos_lt_top (j : ℕ) (vQ : RationalPlace) :
    0 < packetMeasure D j vQ (region D j vQ) ∧ packetMeasure D j vQ (region D j vQ) < ⊤ := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketLogShell.productMeasure_region_pos_lt_top D p j
  | infinite => exact IutInitialThetaArchimedeanPacketRegion.productMeasure_region_pos_lt_top D j

theorem hull_region_subset (j : ℕ) (vQ : RationalPlace) :
    IutInitialThetaAdelicPacketHull.region D j vQ ⊆ region D j vQ := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketLogShell.hull_region_subset D p j
  | infinite => exact Set.Subset.rfl

theorem source_region_subset (j : ℕ) (vQ : RationalPlace) :
    IutInitialThetaAdelicPacketRegion.region D j vQ ⊆ region D j vQ :=
  (IutInitialThetaAdelicPacketHull.source_subset_region D j vQ).trans (hull_region_subset D j vQ)

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

theorem hull_containerRegion_subset (j : ℕ) :
    IutInitialThetaAdelicPacketHull.containerRegion D j ⊆ containerRegion D j :=
  fun _ hx vQ => hull_region_subset D j vQ (hx vQ)

theorem containerRegion_nonempty (j : ℕ) : (containerRegion D j).Nonempty :=
  (IutInitialThetaAdelicPacketHull.containerRegion_nonempty D j).mono (hull_containerRegion_subset D j)

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
  | .finite p => IutInitialThetaFinitePacketLogShell.packetLogVolume D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j

theorem packetLogVolume_nonneg (j : ℕ) (vQ : RationalPlace) : 0 ≤ packetLogVolume D j vQ := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketLogShell.packetLogVolume_nonneg D p j
  | infinite => exact IutInitialThetaArchimedeanPacketRegion.packetLogVolume_nonneg D j

theorem packetLogVolume_eq_zero_of_not_exceptional (j : ℕ) (vQ : RationalPlace)
    (hv : vQ ∉ exceptionalPlaces D) : packetLogVolume D j vQ = 0 := by
  cases vQ with
  | infinite => exact False.elim (hv (Finset.mem_insert_self _ _))
  | finite p =>
    change IutInitialThetaFinitePacketLogShell.packetLogVolume D p j = 0
    rw [IutInitialThetaFinitePacketLogShell.packetLogVolume_eq_productMeasure_log]
    have he := region_eq_integralRegion_of_not_exceptional D j (.finite p) hv
    change IutInitialThetaFinitePacketLogShell.region D p j =
      IutInitialThetaFinitePacketRegion.integralRegion D p j at he
    rw [he, IutInitialThetaFinitePacketRegion.productMeasure_integralRegion]
    simp only [ENNReal.toReal_one, Real.log_one, zero_div]

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

theorem globalLogVolume_nonneg (j : ℕ) : 0 ≤ globalLogVolume D j := by
  rw [globalLogVolume_eq_sum]
  exact Finset.sum_nonneg fun vQ _ => packetLogVolume_nonneg D j vQ

theorem hull_packetLogVolume_le (j : ℕ) (vQ : RationalPlace) :
    IutInitialThetaAdelicPacketHull.packetLogVolume D j vQ ≤ packetLogVolume D j vQ := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketLogShell.hull_packetLogVolume_le D p j
  | infinite => exact le_refl _

theorem hull_globalLogVolume_le (j : ℕ) :
    IutInitialThetaAdelicPacketHull.globalLogVolume D j ≤ globalLogVolume D j :=
  finsum_le_finsum' (IutInitialThetaAdelicPacketHull.packetLogVolume_finite_support D j)
    (packetLogVolume_finite_support D j) (hull_packetLogVolume_le D j)

def processionLogVolume : ℝ :=
  (∑ i : IutInitialThetaFinitePacketRegion.Index D, globalLogVolume D (i.val + 1)) /
    (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ)

theorem processionLogVolume_nonneg : 0 ≤ processionLogVolume D :=
  div_nonneg (Finset.sum_nonneg fun i _ => globalLogVolume_nonneg D (i.val + 1)) (Nat.cast_nonneg _)

theorem hull_processionLogVolume_le :
    IutInitialThetaAdelicPacketHull.processionLogVolume D ≤ processionLogVolume D :=
  div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => hull_globalLogVolume_le D (i.val + 1)) (Nat.cast_nonneg _)

end
end JoshiTeich.Act1Scene1.IutInitialThetaAdelicLogShell
