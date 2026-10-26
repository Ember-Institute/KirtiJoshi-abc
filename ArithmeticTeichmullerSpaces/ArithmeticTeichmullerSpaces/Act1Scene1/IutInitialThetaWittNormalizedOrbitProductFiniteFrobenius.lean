import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNormalizedOrbitProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNormalizedOrbitFactorFrobenius
import Mathlib.Topology.Sequences

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-NORMALIZED-ORBIT-PRODUCT-FINITE-FROBENIUS
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, finite Frobenius shift of primitive factors.
fidelity: proves the exact finite identity
`phi(P_N) * f_0 = P_(N+1)`, then passes to the common-ring limit using
the already proved partial-product convergence and Frobenius continuity.
This avoids any unproved infinite-product rearrangement.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the resulting product equation is only for
the actual normalized orbit product. It does not identify that product
with the Tate period or prove the full eigen-kernel identity.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittNormalizedOrbitProductFiniteFrobenius

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius
open InitialThetaWittNormalizedOrbitProduct
open InitialThetaWittNormalizedOrbitFactorFrobenius
open Filter
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem finite_frobenius_shift (N : ℕ) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
        (partialProduct D w N) * factor D w 0 =
      partialProduct D w (N + 1) := by
  rw [partialProduct, map_prod]
  simp_rw [frobenius_factor D w]
  change (∏ x ∈ Finset.range N, factor D w (x + 1)) * factor D w 0 =
    ∏ x ∈ Finset.range (N + 1), factor D w x
  rw [Finset.prod_range_succ']

theorem product_frobenius_mul_factor_zero :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) * factor D w 0 =
      product D w := by
  have hphi : Tendsto
      (fun N => InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
        (partialProduct D w N)) atTop
        (𝓝 (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w))) :=
    ((InitialThetaWittAllRadiusFrobenius.frobenius_continuous D w).tendsto
      (product D w)).comp (partial_tendsto D w)
  have hmul : Tendsto
      (fun N => InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
        (partialProduct D w N) * factor D w 0) atTop
        (𝓝 (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w) *
          factor D w 0)) := hphi.mul tendsto_const_nhds
  have hshift : Tendsto (fun N => partialProduct D w (N + 1)) atTop
      (𝓝 (product D w)) :=
    (partial_tendsto D w).comp (tendsto_add_atTop_nat 1)
  have heq : (fun N => InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
      (partialProduct D w N) * factor D w 0) =ᶠ[atTop]
      (fun N => partialProduct D w (N + 1)) :=
    Filter.Eventually.of_forall (finite_frobenius_shift D w)
  exact tendsto_nhds_unique (hmul.congr' heq) hshift

end
end JoshiTeich.Act1Scene1.InitialThetaWittNormalizedOrbitProductFiniteFrobenius
