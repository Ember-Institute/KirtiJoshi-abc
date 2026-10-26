import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNormalizedOrbitProductQuotientFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ORBIT-PRODUCT-SIMPLE-THETA-ZERO
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, primitive zeros in the complete period ring.
fidelity: theta applied to the Frobenius translate of the actual orbit
product is a convergent nonzero product of the positive-index factors.
Summability follows from the original contractive theta map and the
proved coordinate correction bounds. Thus the primitive quotient has
nonzero theta value, and the original product is not divisible by xi^2.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; only the original untilt and primitive are
used. No Tate-period identification or full eigen-kernel law is input.
Original topology and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittOrbitProductSimpleThetaZero

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittNormalizedOrbitProduct
open InitialThetaWittNormalizedOrbitProductQuotientFrobenius
open InitialThetaWittNormalizedOrbitFactorFrobenius
open InitialThetaWittThetaEvaluation InitialThetaWittThetaBound
open InitialThetaWittThetaPrincipalKernel
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

theorem evaluation_scaleUnit_ne_zero :
    evaluation D w (scaleUnit D w : Carrier D w) ≠ 0 :=
  ((scaleUnit D w).isUnit.map (evaluation D w)).ne_zero

theorem evaluation_scaleUnit :
    evaluation D w (scaleUnit D w : Carrier D w) =
      -1 / (Arithmetic.residueChar w.1 : Untilt D w) := by
  have h := congrArg (evaluation D w) (scaleUnit_mul_prime D w)
  rw [map_mul, map_natCast, map_neg, map_one] at h
  exact (eq_div_iff (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)).mpr h

theorem evaluation_positive_factor (n : ℕ) :
    evaluation D w (factor D w (n + 1)) =
      1 - (Arithmetic.residueChar w.1 : Untilt D w) ^
        (Arithmetic.residueChar w.1 ^ (n + 1)) / Arithmetic.residueChar w.1 := by
  rw [factor_eq_one_add, map_add, map_one, correction, map_mul, map_pow,
    evaluation_scaleUnit, InitialThetaWittFrobeniusThetaOrbit.evaluation_teichPrime]
  ring

theorem evaluation_positive_factor_ne_zero (n : ℕ) :
    evaluation D w (factor D w (n + 1)) ≠ 0 := by
  rw [factor, map_mul]
  exact mul_ne_zero (evaluation_scaleUnit_ne_zero D w)
    (InitialThetaWittFrobeniusThetaOrbit.evaluation_primitiveOrbit_ne_zero D w
      (n + 1) (Nat.succ_pos n))

theorem summable_evaluation_tail_correction :
    Summable (fun n : ℕ => ‖evaluation D w (correction D w (n + 1))‖) := by
  have h := (summable_nat_add_iff 1).mpr (summable_correction_norm D w (radius D w))
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  exact InitialThetaWittThetaEvaluation.evaluation_norm_le D w _

def untiltTailProduct : Untilt D w :=
  ∏' n : ℕ, (1 + evaluation D w (correction D w (n + 1)))

theorem untiltTail_hasProd :
    HasProd (fun n : ℕ => evaluation D w (factor D w (n + 1)))
      (untiltTailProduct D w) := by
  have h := (multipliable_one_add_of_summable (summable_evaluation_tail_correction D w)).hasProd
  simpa only [factor_eq_one_add, map_add, map_one, untiltTailProduct] using h

theorem untiltTailProduct_ne_zero : untiltTailProduct D w ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable
    (fun n => ?_) (summable_evaluation_tail_correction D w)
  simpa only [factor_eq_one_add, map_add, map_one] using
    evaluation_positive_factor_ne_zero D w n

theorem evaluation_frobenius_partialProduct (N : ℕ) :
    evaluation D w (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
      (partialProduct D w N)) =
      ∏ n ∈ Finset.range N, evaluation D w (factor D w (n + 1)) := by
  rw [partialProduct, map_prod, map_prod]
  simp_rw [frobenius_factor D w]

theorem evaluation_frobenius_product :
    evaluation D w (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
      (product D w)) = untiltTailProduct D w := by
  have hphi := ((InitialThetaWittAllRadiusFrobenius.frobenius_continuous D w).tendsto
    (product D w)).comp (partial_tendsto D w)
  have he := ((InitialThetaWittThetaEvaluation.evaluation_continuous D w).tendsto
    (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w))).comp hphi
  have ht := (untiltTail_hasProd D w).tendsto_prod_nat
  have hs : Tendsto (fun N => evaluation D w
      (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (partialProduct D w N)))
      atTop (𝓝 (evaluation D w
        (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (product D w)))) := he
  simp only [evaluation_frobenius_partialProduct] at hs
  exact tendsto_nhds_unique hs ht

theorem evaluation_productQuotient :
    evaluation D w (primitiveProductQuotient D w) =
      evaluation D w (scaleUnit D w : Carrier D w) * untiltTailProduct D w := by
  rw [productQuotient_eq_frobenius_scaled, map_mul, evaluation_frobenius_product]

theorem evaluation_productQuotient_ne_zero :
    evaluation D w (primitiveProductQuotient D w) ≠ 0 := by
  rw [evaluation_productQuotient]
  exact mul_ne_zero (evaluation_scaleUnit_ne_zero D w) (untiltTailProduct_ne_zero D w)

theorem primitive_not_dvd_productQuotient :
    ¬ primitive D w ∣ primitiveProductQuotient D w := by
  exact fun h => evaluation_productQuotient_ne_zero D w
    ((evaluation_eq_zero_iff_dvd D w _).mpr h)

theorem primitive_sq_not_dvd_product : ¬ primitive D w ^ 2 ∣ product D w := by
  rintro ⟨a, ha⟩
  apply primitive_not_dvd_productQuotient D w
  refine ⟨a, ?_⟩
  apply (InitialThetaWittPrincipalIdealClosed.multiplication_isUniformEmbedding D w
    (primitive D w) (primitive_ne_zero D w)).injective
  change primitive D w * primitiveProductQuotient D w = primitive D w * _
  rw [primitive_mul_productQuotient, ha, pow_two]
  ring

end
end JoshiTeich.Act1Scene1.InitialThetaWittOrbitProductSimpleThetaZero
