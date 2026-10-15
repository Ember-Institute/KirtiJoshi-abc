import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperLogShellBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensor
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorLogShellHull

/-!
source-id: JT-SCENE1-PAPER-WITNESS-TENSOR-LOG-SHELL
source: actual full-support paper-normalized witnesses and the tensor
log-shell carrier used by the ordinary hull construction.
fidelity: lifts the factorwise paper-normalized log-shell membership to the
actual pure tensor witness. This is a tensor carrier statement only; it does
not identify the tensor log-shell with H^1_e/BK or with a paper theta locus.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PaperLogWitnessHull
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

local instance paperTensorPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem witness_mem_tensorLogShell
    (v : iutInitialThetaOddModSupportFinset D) :
    witness D n v ∈ (packet D n v).tensorLogShell := by
  apply (packet D n v).pure_mem_lattice
  intro i
  have h := value_mem_logShell D (FullSupportThetaLogHull.sourceAt D n v i)
  rw [Arithmetic.residueChar_eq_of_liesOver
    (FullSupportThetaLogHull.sourceAt_liesOver D n v i)] at h
  exact h

theorem witness_integralHull_le_unitLattice
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).integralHull {witness D n v} ≤ (packet D n v).unitLattice := by
  apply (packet D n v).integralHull_le_unitLattice
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  apply (packet D n v).pure_mem_lattice
  intro i
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [norm_value_eq_qroot_norm]
  exact (iutInitialThetaFullQRoot_norm_lt_one D _).le

theorem witness_integralHull_le_tensorLogShell
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).integralHull {witness D n v} ≤ (packet D n v).tensorLogShell := by
  apply (packet D n v).integralHull_le_tensorLogShell
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  change witness D n v ∈ (packet D n v).tensorLogShell
  exact witness_mem_tensorLogShell D n v

end
end JoshiTeich.Act1Scene1.PaperLogWitnessHull
