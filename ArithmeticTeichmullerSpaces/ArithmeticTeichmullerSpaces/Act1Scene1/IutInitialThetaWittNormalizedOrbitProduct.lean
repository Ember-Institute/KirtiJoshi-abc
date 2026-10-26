import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenKernelFiniteDivision
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-NORMALIZED-ORBIT-PRODUCT
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, Frobenius primitive factors in the period ring.
fidelity: normalizes each actual phi^n(xi) by the unit -1/p.
Its deviation from one has exact rho norm q^(p^n)/rho, where q is the
original untilt norm of p. Geometric domination proves a nonzero product
at every radius. Simultaneous partial products and the original closed
diagonal carrier give one nonzero common-ring limit.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no product convergence or nonvanishing law
is input. Full Tate-period identification remains open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittNormalizedOrbitProduct

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittFrobeniusThetaOrbit InitialThetaWittEigenKernelFiniteDivision
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

def primeUnit : (Carrier D w)ˣ := Classical.choose (prime_isUnit D w)

theorem primeUnit_val : (primeUnit D w : Carrier D w) = Arithmetic.residueChar w.1 :=
  Classical.choose_spec (prime_isUnit D w)

def scaleUnit : (Carrier D w)ˣ := -(primeUnit D w)⁻¹

theorem scaleUnit_mul_prime : (scaleUnit D w : Carrier D w) * Arithmetic.residueChar w.1 = -1 := by
  rw [← primeUnit_val]
  change -((primeUnit D w)⁻¹ : (Carrier D w)ˣ).val * (primeUnit D w).val = -1
  rw [neg_mul, Units.inv_mul]

def factor (n : ℕ) : Carrier D w := (scaleUnit D w : Carrier D w) * primitiveOrbit D w n

def correction (n : ℕ) : Carrier D w :=
  (scaleUnit D w : Carrier D w) * teichPrime D w ^ (Arithmetic.residueChar w.1 ^ n)

theorem factor_eq_one_add (n : ℕ) : factor D w n = 1 + correction D w n := by
  simp only [factor, correction, primitiveOrbit_eq, mul_sub, scaleUnit_mul_prime,
    sub_neg_eq_add, add_comm]

def primeNorm : ℝ := ‖(Arithmetic.residueChar w.1 : InitialThetaWittThetaBound.Untilt D w)‖

theorem primeNorm_pos_lt_one : 0 < primeNorm D w ∧ primeNorm D w < 1 :=
  (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out

theorem norm_evaluate_teichPrime (ρ : Radius) : ‖evaluate D w ρ (teichPrime D w)‖ = primeNorm D w := by
  change ‖InitialThetaWittRhoExpansion.ainfMap D w ρ
    (InitialThetaBoundedWittLocalization.teichVarpi D w)‖ = _
  rw [InitialThetaBoundedWittLocalization.teichVarpi,
    InitialThetaWittTateLogarithm.norm_ainf_teichmuller,
    InitialThetaBoundedWittLocalization.varpi, InitialThetaTiltFontaine.integralLift_norm]
  rfl

theorem norm_evaluate_scaleUnit (ρ : Radius) :
    ‖evaluate D w ρ (scaleUnit D w : Carrier D w)‖ = 1 / ρ.val.toReal := by
  have h := congrArg (fun z : Carrier D w => ‖evaluate D w ρ z‖) (scaleUnit_mul_prime D w)
  rw [map_mul, norm_mul, map_neg, map_one, norm_neg, norm_one] at h
  have hp : ‖evaluate D w ρ (Arithmetic.residueChar w.1 : Carrier D w)‖ = ρ.val.toReal := by
    simpa only [map_natCast] using InitialThetaWittRhoCompletion.inclusion_prime_norm D w ρ
  rw [hp] at h
  exact (eq_div_iff (ENNReal.toReal_pos ρ.property.1.ne'
    (ρ.property.2.trans ENNReal.one_lt_top).ne).ne').mpr h

theorem norm_evaluate_correction (ρ : Radius) (n : ℕ) :
    ‖evaluate D w ρ (correction D w n)‖ =
      (1 / ρ.val.toReal) * primeNorm D w ^ (Arithmetic.residueChar w.1 ^ n) := by
  rw [correction, map_mul, norm_mul, map_pow, norm_pow,
    norm_evaluate_scaleUnit, norm_evaluate_teichPrime]

theorem summable_correction_norm (ρ : Radius) :
    Summable (fun n : ℕ => ‖evaluate D w ρ (correction D w n)‖) := by
  have hq := primeNorm_pos_lt_one D w
  have hs := (summable_geometric_of_lt_one hq.1.le hq.2).mul_left (1 / ρ.val.toReal)
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_evaluate_correction]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hq.1.le hq.2.le (n.lt_pow_self (Arithmetic.residueChar_prime w.1).one_lt).le)
    (one_div_nonneg.mpr ENNReal.toReal_nonneg)

theorem evaluate_factor_ne_zero (ρ : Radius) (n : ℕ) : evaluate D w ρ (factor D w n) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [factor, map_mul, norm_mul]
  apply mul_ne_zero
  · rw [norm_evaluate_scaleUnit]
    exact one_div_ne_zero (ENNReal.toReal_pos ρ.property.1.ne'
      (ρ.property.2.trans ENNReal.one_lt_top).ne).ne'
  · apply norm_ne_zero_iff.mpr
    intro h
    apply primitiveOrbit_ne_zero D w n
    apply InitialThetaWittRadiusFaithfulness.evaluate_injective D w ρ
    exact h.trans (map_zero _).symm

def completedProduct (ρ : Radius) : InitialThetaWittRhoCompletion.Completed D w ρ :=
  ∏' n : ℕ, (1 + evaluate D w ρ (correction D w n))

theorem completed_hasProd (ρ : Radius) :
    HasProd (fun n => evaluate D w ρ (factor D w n)) (completedProduct D w ρ) := by
  have h := (multipliable_one_add_of_summable (summable_correction_norm D w ρ)).hasProd
  simpa only [factor_eq_one_add, map_add, map_one, completedProduct] using h

theorem completedProduct_ne_zero (ρ : Radius) : completedProduct D w ρ ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable
    (fun n => ?_) (summable_correction_norm D w ρ)
  simpa only [factor_eq_one_add, map_add, map_one] using evaluate_factor_ne_zero D w ρ n

def partialProduct (N : ℕ) : Carrier D w := ∏ n ∈ Finset.range N, factor D w n

theorem ambient_partial_tendsto :
    Tendsto (fun N => (partialProduct D w N).val) atTop (𝓝 (fun ρ => completedProduct D w ρ)) := by
  apply tendsto_pi_nhds.mpr
  intro ρ
  change Tendsto (fun N => evaluate D w ρ (partialProduct D w N)) atTop (𝓝 (completedProduct D w ρ))
  simpa only [partialProduct, map_prod] using (completed_hasProd D w ρ).tendsto_prod_nat

theorem product_mem : (fun ρ => completedProduct D w ρ) ∈ commonSubring D w := by
  exact (Subring.isClosed_topologicalClosure (diagonal D w).range).mem_of_tendsto
    (ambient_partial_tendsto D w) (Eventually.of_forall (fun N => (partialProduct D w N).property))

def product : Carrier D w := ⟨fun ρ => completedProduct D w ρ, product_mem D w⟩

theorem evaluate_product (ρ : Radius) : evaluate D w ρ (product D w) = completedProduct D w ρ := rfl

theorem partial_tendsto : Tendsto (partialProduct D w) atTop (𝓝 (product D w)) := by
  apply tendsto_subtype_rng.mpr
  exact ambient_partial_tendsto D w

theorem product_ne_zero : product D w ≠ 0 := by
  intro h
  apply completedProduct_ne_zero D w (InitialThetaWittThetaBound.radius D w)
  have he := congrArg (evaluate D w (InitialThetaWittThetaBound.radius D w)) h
  simpa only [evaluate_product, map_zero] using he

end
end JoshiTeich.Act1Scene1.InitialThetaWittNormalizedOrbitProduct
