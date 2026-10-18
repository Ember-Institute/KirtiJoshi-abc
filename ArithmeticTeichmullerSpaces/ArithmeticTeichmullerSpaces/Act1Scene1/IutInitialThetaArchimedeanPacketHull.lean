import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensorRadialHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdelicPacketHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-ARCHIMEDEAN-PACKET-HULL
source: reference LocalConstruct/Admissible, exists_leastHull_infinite;
Concrete/Container, hull; Cor312/HolomorphicHull radial hull class at infinity.
fidelity: applies the constructed radial hull to every actual infinite-place
component and proves its product is the least product of positive radial
regions containing the source. Identifies the previous adelic hull at infinity
with this actual least-hull product and preserves its exact Haar/log formulas.
This proves local container hull identity, not paper theta-locus identity.
Original consumer proofs; no reference code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaArchimedeanPacketHull

open NumberField MeasureTheory
open IutInitialThetaArchimedeanPacketRegion
open scoped BigOperators Pointwise Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def componentHull (j : ℕ) (c : Tuple D j) : Set (LocalArchimedean.Tensor c) :=
  LocalArchimedean.radialHull c
    (LocalArchimedean.factorOrbit c (LocalArchimedean.archLogShell c))

theorem componentHull_eq_archLogShell (j : ℕ) (c : Tuple D j) :
    componentHull D j c = LocalArchimedean.archLogShell c := by
  rw [componentHull, LocalArchimedean.factorOrbit_archLogShell,
    LocalArchimedean.radialHull_archLogShell]

def region (j : ℕ) : Set (Total D j) := Set.pi Set.univ (componentHull D j)

theorem region_eq_source (j : ℕ) :
    region D j = IutInitialThetaArchimedeanPacketRegion.region D j := by
  rw [IutInitialThetaArchimedeanPacketRegion.region_eq_shell_product]
  unfold region
  congr 1
  funext c
  exact componentHull_eq_archLogShell D j c

theorem region_le_radial_product (j : ℕ) (t : Tuple D j → ℝ) (ht : ∀ c, 0 < t c)
    (hUt : IutInitialThetaArchimedeanPacketRegion.region D j ⊆
      Set.pi Set.univ (fun c => LocalArchimedean.radialRegion c (t c))) :
    region D j ⊆ Set.pi Set.univ (fun c => LocalArchimedean.radialRegion c (t c)) := by
  have hcoord := Set.pi_subset_pi_iff.mp hUt
  have hne : (IutInitialThetaArchimedeanPacketRegion.region D j).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hpos := (productMeasure_region_pos_lt_top D j).1
    rw [he, measure_empty] at hpos
    exact (lt_irrefl _ hpos)
  have hUt' : ∀ c : Tuple D j,
      LocalArchimedean.factorOrbit c (LocalArchimedean.archLogShell c) ⊆
        LocalArchimedean.radialRegion c (t c) := by
    rcases hcoord with h | h
    · exact fun c => h c (Set.mem_univ c)
    · exact False.elim (hne.ne_empty h)
  exact Set.pi_mono fun c _ => LocalArchimedean.radialHull_le_radialRegion c
    (LocalArchimedean.isCompact_factorOrbit_archLogShell c).isBounded
    (LocalArchimedean.factorOrbit_archLogShell_haar_pos_lt_top c).1 (ht c) (hUt' c)

theorem region_isPositiveRadialProduct (j : ℕ) :
    ∃ t : Tuple D j → ℝ, (∀ c, 0 < t c) ∧
      region D j = Set.pi Set.univ (fun c => LocalArchimedean.radialRegion c (t c)) := by
  refine ⟨fun _ => Real.pi ^ (j + 1), fun _ => pow_pos Real.pi_pos _, ?_⟩
  unfold region
  congr 1
  funext c
  rw [componentHull_eq_archLogShell]
  simp only [LocalArchimedean.archLogShell, LocalArchimedean.radialRegion, Fintype.card_fin]

theorem adelicHull_infinite_eq (j : ℕ) :
    IutInitialThetaAdelicPacketHull.region D j .infinite = region D j :=
  (region_eq_source D j).symm

theorem region_isCompact (j : ℕ) : IsCompact (region D j) := by
  rw [region_eq_source]
  exact IutInitialThetaArchimedeanPacketRegion.region_isCompact D j

theorem productMeasure_region_pos_lt_top (j : ℕ) :
    0 < productMeasure D j (region D j) ∧ productMeasure D j (region D j) < ⊤ := by
  rw [region_eq_source]
  exact IutInitialThetaArchimedeanPacketRegion.productMeasure_region_pos_lt_top D j

theorem componentHull_logVolume (j : ℕ) (c : Tuple D j) :
    LocalArchimedean.normalizationLogVolume c (componentHull D j c) =
      ((j + 1 : ℕ) : ℝ) * Real.log Real.pi := by
  rw [componentHull_eq_archLogShell, LocalArchimedean.normalizationLogVolume_archLogShell,
    Fintype.card_fin]

def packetLogVolume (j : ℕ) : ℝ := ∑ c : Tuple D j,
  tupleWeight D j c * LocalArchimedean.normalizationLogVolume c (componentHull D j c)

theorem packetLogVolume_eq_source (j : ℕ) :
    packetLogVolume D j = IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  simp only [packetLogVolume, IutInitialThetaArchimedeanPacketRegion.packetLogVolume,
    componentHull_eq_archLogShell, LocalArchimedean.factorOrbit_archLogShell]

theorem packetLogVolume_eq (j : ℕ) :
    packetLogVolume D j = ((j + 1 : ℕ) : ℝ) * Real.log Real.pi := by
  rw [packetLogVolume_eq_source, IutInitialThetaArchimedeanPacketRegion.packetLogVolume_eq]

theorem adelicHull_infinite_logVolume_eq (j : ℕ) :
    IutInitialThetaAdelicPacketHull.packetLogVolume D j .infinite = packetLogVolume D j :=
  (packetLogVolume_eq_source D j).symm

end
end JoshiTeich.Act1Scene1.IutInitialThetaArchimedeanPacketHull
