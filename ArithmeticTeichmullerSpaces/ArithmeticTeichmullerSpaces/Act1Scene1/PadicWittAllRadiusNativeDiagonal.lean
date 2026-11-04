import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusCompletion
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoSourceEmbedding

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-ALL-RADIUS-NATIVE-DIAGONAL
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the original
bounded Witt subring in the product of all rho completions.
fidelity: records the original standard diagonal as a bare function built
from the separately identified fixed-radius inclusion functions. It rewrites
membership in the original common closure using that same diagonal function.
Every declaration depends only on p and its primality instance. The original
diagonal, commonSubring, Carrier, completion maps and norms are unchanged.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; actual-to-standard transport, paper B marking and
period/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittAllRadiusCompletion

open scoped Topology
noncomputable section

variable (p : ℕ) [Fact p.Prime]

def diagonalFun : PadicBoundedWittLocalization.Ring p → Product p :=
  fun x ρ => PadicWittRhoCompletion.inclusionFun p ρ x

theorem diagonal_eq_diagonalFun :
    (diagonal p : PadicBoundedWittLocalization.Ring p → Product p) =
      diagonalFun p := by
  funext x ρ
  exact congrFun (PadicWittRhoCompletion.inclusion_eq_inclusionFun p ρ) x

theorem mem_common_iff_mem_closure_diagonalFun (x : Product p) :
    x ∈ commonSubring p ↔ x ∈ closure (Set.range (diagonalFun p)) := by
  change x ∈ closure (Set.range (diagonal p)) ↔ _
  rw [diagonal_eq_diagonalFun p]

theorem commonSubring_carrier_eq_closure_diagonalFun :
    (commonSubring p : Set (Product p)) = closure (Set.range (diagonalFun p)) := by
  ext x
  exact mem_common_iff_mem_closure_diagonalFun p x

theorem inclusion_val_eq_diagonalFun (x : PadicBoundedWittLocalization.Ring p) :
    (inclusion p x).val = diagonalFun p x :=
  congrFun (diagonal_eq_diagonalFun p) x

end
end JoshiTeich.Act1Scene1.PadicWittAllRadiusCompletion
