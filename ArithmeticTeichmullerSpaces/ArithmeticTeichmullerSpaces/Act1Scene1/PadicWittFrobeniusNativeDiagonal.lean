import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusNativeDiagonal
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusFrobenius

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-NATIVE-DIAGONAL
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius on
the original bounded Witt diagonal in the product of all rho completions.
fidelity: rewrites the existing product Frobenius and inverse identities
using the original native diagonal function. It records the subtype values
of the existing common-ring Frobenius and inverse. Every declaration depends
only on p and its primality instance. The original functions, carriers and
diagonal are unchanged.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; actual-to-standard comparison and paper B marking,
period and BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittProductFrobenius

noncomputable section
variable (p : ℕ) [Fact p.Prime]

theorem productEquiv_diagonalFun (x : PadicBoundedWittLocalization.Ring p) :
    productEquiv p (PadicWittAllRadiusCompletion.diagonalFun p x) =
      PadicWittAllRadiusCompletion.diagonalFun p
        (PadicWittRhoFrobenius.frobeniusEquiv p x) := by
  simpa only [PadicWittAllRadiusCompletion.diagonal_eq_diagonalFun p]
    using productEquiv_diagonal p x

theorem productEquiv_symm_diagonalFun (x : PadicBoundedWittLocalization.Ring p) :
    (productEquiv p).symm (PadicWittAllRadiusCompletion.diagonalFun p x) =
      PadicWittAllRadiusCompletion.diagonalFun p
        ((PadicWittRhoFrobenius.frobeniusEquiv p).symm x) := by
  simpa only [PadicWittAllRadiusCompletion.diagonal_eq_diagonalFun p]
    using productEquiv_symm_diagonal p x

end
end JoshiTeich.Act1Scene1.PadicWittProductFrobenius

namespace JoshiTeich.Act1Scene1.PadicWittAllRadiusFrobenius

noncomputable section
variable (p : ℕ) [Fact p.Prime]

-- Freeze the subtype-value reduction before any concrete D,w specialization.
theorem frobeniusEquiv_val (x : PadicWittAllRadiusCompletion.Carrier p) :
    (frobeniusEquiv p x).val =
      PadicWittProductFrobenius.productEquiv p x.val := rfl

theorem frobeniusEquiv_symm_val (x : PadicWittAllRadiusCompletion.Carrier p) :
    ((frobeniusEquiv p).symm x).val =
      (PadicWittProductFrobenius.productEquiv p).symm x.val := rfl

end
end JoshiTeich.Act1Scene1.PadicWittAllRadiusFrobenius
