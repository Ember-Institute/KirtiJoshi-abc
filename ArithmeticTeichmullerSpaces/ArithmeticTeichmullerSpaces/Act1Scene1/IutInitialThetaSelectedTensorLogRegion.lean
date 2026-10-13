import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedLogBallProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndex

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-LOG-REGION
source: actual selected q-root source partitioned by residue prime, its
ordinary logarithm balls, and the local completion tensor lattice/Haar API.
fidelity: constructs the tensor packet from every selected place at one prime,
with a finite bijective enumeration. Its actual logarithm tensor region is
compact open, lies in the tensor log-shell, and has inverse-index Haar volume.
This does not identify that volume with the paper-weighted scalar product,
Bloch-Kato classes, different untilts, or the theta hull.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.SelectedThetaTensor

open JoshiTeich.Prologue
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

def fiber (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) :
    Finset (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  Finset.univ.filter (fun s => s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D ∧
    Arithmetic.residueChar s.1 = p)

/-- A bijection enumerates the entire actual selected prime fibre exactly once. -/
def enumeration (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) :
    Fin (Fintype.card ↥(fiber D p)) ≃ ↥(fiber D p) :=
  (Fintype.equivFin ↥(fiber D p)).symm

def sourceAt (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ)
    (i : Fin (Fintype.card ↥(fiber D p))) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  (enumeration D p i).1

theorem sourceAt_selected_residueChar
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ)
    (i : Fin (Fintype.card ↥(fiber D p))) :
    sourceAt D p i ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D ∧
      Arithmetic.residueChar (sourceAt D p i).1 = p :=
  (Finset.mem_filter.mp (enumeration D p i).2).2

def packet (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) :
    LocalCompletion.Packet ↥D.prime.torsionField p (Fin (Fintype.card ↥(fiber D p))) :=
  ⟨fun i => (sourceAt D p i).1, fun i => (sourceAt_selected_residueChar D p i).2⟩

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]

local instance integralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

def value : (packet D p).Tensor :=
  (packet D p).pure (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D p i))

def region : Submodule ℤ_[p] (packet D p).Tensor :=
  (packet D p).lattice (fun i => iutInitialThetaFullQRootLogBall D (sourceAt D p i))

private theorem scalar_ne_zero (i : Fin (Fintype.card ↥(fiber D p))) :
    iutInitialThetaFullQRootLogValue D (sourceAt D p i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero (sourceAt D p i))

private theorem scalar_norm_le_one (i : Fin (Fintype.card ↥(fiber D p))) :
    ‖iutInitialThetaFullQRootLogValue D (sourceAt D p i)‖ ≤ 1 := by
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact (iutInitialThetaFullQRoot_norm_lt_one D (sourceAt D p i)).le

theorem value_ne_zero : value D p ≠ 0 :=
  LocalCompletion.Packet.pure_ne_zero (packet D p) _ (scalar_ne_zero D p)

theorem value_mem_region : value D p ∈ region D p := by
  apply LocalCompletion.Packet.pure_mem_lattice
  intro i
  exact ⟨1, by simp, mul_one _⟩

theorem region_eq_rootBallLattice : region D p =
    (packet D p).lattice (fun i => iutInitialThetaQRootIntegralBall D (sourceAt D p i)) := by
  unfold region
  simp only [iutInitialThetaFullQRootLogBall_eq_rootBall]

private theorem region_eq_ballLattice : region D p =
    (packet D p).lattice (fun i => Metric.closedBall 0
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)‖) := by
  rw [region_eq_rootBallLattice]
  congr 1
  funext i
  exact LocalPadicLog.mul_image_closedBall _
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero (sourceAt D p i))

theorem region_le_tensorLogShell : region D p ≤ (packet D p).tensorLogShell := by
  apply LocalCompletion.Packet.lattice_mono
  intro i
  have h := iutInitialThetaFullQRootLogBall_subset_logShell D (sourceAt D p i)
  rw [(sourceAt_selected_residueChar D p i).2] at h
  exact h

theorem region_isOpen : IsOpen (region D p : Set (packet D p).Tensor) := by
  rw [region_eq_ballLattice]
  apply LocalCompletion.Packet.lattice_balls_isOpen
  intro i
  exact norm_pos_iff.mpr
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero (sourceAt D p i))

theorem region_isCompact : IsCompact (region D p : Set (packet D p).Tensor) := by
  rw [region_eq_ballLattice]
  apply LocalCompletion.Packet.lattice_balls_isCompact
  · intro i
    exact norm_pos_iff.mpr
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero (sourceAt D p i))
  · intro i
    exact (iutInitialThetaFullQRoot_norm_lt_one D (sourceAt D p i)).le

def regionIndex : ℕ :=
  (packet D p).scalarIndex (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D p i))

theorem regionIndex_pos : 0 < regionIndex D p :=
  LocalCompletion.Packet.scalarIndex_pos (packet D p) _ (scalar_ne_zero D p)

theorem region_normalizedHaar_eq_inv_index :
    (packet D p).normalizedHaar (region D p) = (regionIndex D p : ENNReal)⁻¹ :=
  LocalCompletion.Packet.normalizedHaar_scalarLattice_eq_inv_index (packet D p) _
    (scalar_ne_zero D p) (scalar_norm_le_one D p)

theorem region_normalizedHaar_pos_le_one :
    0 < (packet D p).normalizedHaar (region D p) ∧
      (packet D p).normalizedHaar (region D p) ≤ 1 := by
  rw [region_normalizedHaar_eq_inv_index]
  constructor
  · exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  · apply ENNReal.inv_le_one.mpr
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (regionIndex_pos D p).ne'

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
