import ArithmeticTeichmullerSpaces.Act1Scene1.MultiplicativeNormDivisionLimit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNormalizedOrbitProduct
import Mathlib.Topology.UniformSpace.Pi

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-KERNEL-INFINITE-DIVISION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`,
primitive Frobenius zeros of the full phi=p theta kernel.
fidelity: constructs exact finite quotients using the proved orbit
divisibility and the original normalizing unit. At every radius their
divisors converge to the proved nonzero product. The multiplicative-norm
division estimate makes the quotients Cauchy in the original common
uniformity. Completeness gives a unique quotient by the actual infinite
product for every full eigen theta-kernel element.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no infinite-divisibility law is input. The
product is not identified with the Tate period; the full Tate kernel
identity remains open. Original carrier and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelInfiniteDivision

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittEigenRadiusDynamics InitialThetaWittEigenKernelFiniteDivision
open InitialThetaWittNormalizedOrbitProduct InitialThetaWittThetaEvaluation
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

theorem partial_eq_scaled_finiteProduct (N : ℕ) :
    partialProduct D w N = (scaleUnit D w : Carrier D w) ^ N * finiteProduct D w (Finset.range N) := by
  simp only [partialProduct, factor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, finiteProduct]

theorem partial_dvd_eigen (x : Eigen D w) (hx : evaluation D w x.val = 0) (N : ℕ) :
    partialProduct D w N ∣ x.val := by
  rw [partial_eq_scaled_finiteProduct]
  exact ((scaleUnit D w).isUnit.pow N).mul_left_dvd.mpr (finiteProduct_dvd_eigen D w _ x hx)

theorem evaluate_partial_ne_zero (ρ : Radius) (N : ℕ) : evaluate D w ρ (partialProduct D w N) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [partialProduct, map_prod, norm_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun n _ => norm_ne_zero_iff.mpr (evaluate_factor_ne_zero D w ρ n))

def finiteQuotient (x : Eigen D w) (hx : evaluation D w x.val = 0) (N : ℕ) : Carrier D w :=
  Classical.choose (partial_dvd_eigen D w x hx N)

theorem partial_mul_finiteQuotient (x : Eigen D w) (hx : evaluation D w x.val = 0) (N : ℕ) :
    partialProduct D w N * finiteQuotient D w x hx N = x.val :=
  (Classical.choose_spec (partial_dvd_eigen D w x hx N)).symm

theorem coordinateQuotient_cauchy (x : Eigen D w) (hx : evaluation D w x.val = 0) (ρ : Radius) :
    CauchySeq (fun N => evaluate D w ρ (finiteQuotient D w x hx N)) := by
  apply MultiplicativeNormDivisionLimit.cauchySeq_quotient
    (fun N => evaluate D w ρ (partialProduct D w N)) _ (evaluate D w ρ x.val) (completedProduct D w ρ)
  · exact evaluate_partial_ne_zero D w ρ
  · exact completedProduct_ne_zero D w ρ
  · simpa only [evaluate_product, Function.comp_def] using
      ((evaluate_continuous D w ρ).tendsto (product D w)).comp (partial_tendsto D w)
  · intro N
    rw [← map_mul, partial_mul_finiteQuotient]

theorem finiteQuotient_cauchy (x : Eigen D w) (hx : evaluation D w x.val = 0) :
    CauchySeq (finiteQuotient D w x hx) := by
  apply isUniformEmbedding_subtype_val.isUniformInducing.cauchy_map_iff.mp
  rw [Filter.map_map]
  apply (cauchy_pi_iff' (l := Filter.map (fun N =>
    fun ρ => evaluate D w ρ (finiteQuotient D w x hx N)) Filter.atTop)).mpr
  intro ρ
  rw [Filter.map_map]
  change CauchySeq (fun N => evaluate D w ρ (finiteQuotient D w x hx N))
  exact coordinateQuotient_cauchy D w x hx ρ

theorem exists_product_quotient_limit (x : Eigen D w) (hx : evaluation D w x.val = 0) :
    ∃ y : Carrier D w, Tendsto (finiteQuotient D w x hx) atTop (𝓝 y) ∧ product D w * y = x.val := by
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (finiteQuotient_cauchy D w x hx)
  refine ⟨y, hy, ?_⟩
  have h := (partial_tendsto D w).mul hy
  simp only [partial_mul_finiteQuotient] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem existsUnique_product_quotient (x : Eigen D w) (hx : evaluation D w x.val = 0) :
    ∃! y : Carrier D w, product D w * y = x.val := by
  obtain ⟨y, _, hy⟩ := exists_product_quotient_limit D w x hx
  refine ⟨y, hy, ?_⟩
  intro z hz
  apply (InitialThetaWittPrincipalIdealClosed.multiplication_isUniformEmbedding D w
    (product D w) (product_ne_zero D w)).injective
  exact hz.trans hy.symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelInfiniteDivision
