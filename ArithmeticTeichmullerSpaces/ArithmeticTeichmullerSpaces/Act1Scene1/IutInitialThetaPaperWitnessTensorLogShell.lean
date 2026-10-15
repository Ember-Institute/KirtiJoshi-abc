import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperLogShellBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensor

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

end
end JoshiTeich.Act1Scene1.PaperLogWitnessHull
