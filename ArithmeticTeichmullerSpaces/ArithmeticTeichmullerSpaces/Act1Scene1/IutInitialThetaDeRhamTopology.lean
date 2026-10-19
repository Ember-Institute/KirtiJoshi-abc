import ArithmeticTeichmullerSpaces.Act1Scene1.AdicNormedIntegers
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamValuation
import Mathlib.Data.Int.WithZero

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-TOPOLOGY
source: Joshi II eta_K, primitive kernel and B_dR (838, 932, 1069--1076);
Joshi III local Hodge rings; Mathlib adic and normed-field completeness.
fidelity: equips the original actual BDeRham field with the primitive-adic
norm exp(-1) -> 1/2, and the original plus ring with its induced norm.
The original kernel powers are exactly its norm balls; their adic completeness
proves completeness of the same plus ring and the same original field.
This norm is primitive-adic. No Frechet/rho or untilt-norm identification
and no theta-locus identity is asserted. Original proofs; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology

open JoshiTeich.Prologue InitialThetaDeRhamCompletion InitialThetaDeRhamField
open InitialThetaDeRhamValuation
open scoped WithZero NNReal Topology
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

def valueEmbedding : ℤᵐ⁰ →*₀o ℝ≥0 :=
  { WithZeroMulInt.toNNReal (show (2 : ℝ≥0) ≠ 0 by norm_num) with
    monotone' := (WithZeroMulInt.toNNReal_strictMono (show (1 : ℝ≥0) < 2 by norm_num)).monotone }

theorem valueEmbedding_strictMono : StrictMono (valueEmbedding) :=
  WithZeroMulInt.toNNReal_strictMono (show (1 : ℝ≥0) < 2 by norm_num)

def normValuation : Valuation (Carrier D w) ℝ≥0 := (valuation D w).map (valueEmbedding)

def absoluteValue : AbsoluteValue (Carrier D w) ℝ where
  toFun x := normValuation D w x
  map_mul' x y := by exact_mod_cast map_mul (normValuation D w) x y
  nonneg' x := (normValuation D w x).property
  eq_zero' x := by
    rw [NNReal.coe_eq_zero]
    change valueEmbedding (valuation D w x) = 0 ↔ x = 0
    rw [← map_zero (valueEmbedding), (valueEmbedding_strictMono).injective.eq_iff]
    exact (valuation D w).zero_iff
  add_le' x y :=
    (NNReal.coe_le_coe.mpr ((normValuation D w).map_add x y)).trans
      (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

instance fieldNormed : NormedField (Carrier D w) := (absoluteValue D w).toNormedField

theorem norm_eq_value (x : Carrier D w) :
    ‖x‖ = (valueEmbedding (valuation D w x) : ℝ) := rfl

theorem norm_le_iff (x y : Carrier D w) : ‖x‖ ≤ ‖y‖ ↔ valuation D w x ≤ valuation D w y := by
  rw [norm_eq_value, norm_eq_value, NNReal.coe_le_coe, (valueEmbedding_strictMono).le_iff_le]

theorem norm_le_one_iff (x : Carrier D w) : ‖x‖ ≤ 1 ↔ valuation D w x ≤ 1 := by
  simpa only [norm_one, map_one] using norm_le_iff D w x 1

instance fieldUltrametric : IsUltrametricDist (Carrier D w) := by
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  exact NNReal.coe_le_coe.mpr ((normValuation D w).map_add x y)

instance fieldValued : Valued (Carrier D w) ℝ≥0 := NormedField.toValued

theorem valued_eq_normValuation :
    (Valued.v : Valuation (Carrier D w) ℝ≥0) = normValuation D w := by
  ext x
  exact norm_eq_value D w x

instance plusNormed : NormedCommRing (Ring D w) :=
  NormedCommRing.induced (Ring D w) (Carrier D w) (algebraMap (Ring D w) (Carrier D w))
    (InitialThetaDeRhamField.algebraMap_injective D w)

theorem inclusion_norm (a : Ring D w) :
    ‖algebraMap (Ring D w) (Carrier D w) a‖ = ‖a‖ := rfl

theorem inclusion_isometry : Isometry (algebraMap (Ring D w) (Carrier D w)) :=
  AddMonoidHomClass.isometry_of_norm _ (inclusion_norm D w)

theorem primitive_norm : ‖algebraMap (Ring D w) (Carrier D w) (primitive D w)‖ = 1 / 2 := by
  rw [norm_eq_value, valuation_primitive]
  norm_num [valueEmbedding, WithZeroMulInt.toNNReal, WithZero.log_exp]

theorem kernel_power_eq_ball (n : ℕ) :
    (((RingHom.ker (theta D w)) ^ n : Ideal (Ring D w)) : Set (Ring D w)) =
      (algebraMap (Ring D w) (Carrier D w)) ⁻¹' Metric.closedBall 0
        (‖algebraMap (Ring D w) (Carrier D w) (primitive D w)‖ ^ n) := by
  ext a
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, ← norm_pow, norm_le_iff,
    map_pow, valuation_primitive]
  exact mem_kernel_pow_iff D w n a

theorem plus_isAdic : IsAdic (RingHom.ker (theta D w)) :=
  AdicNormedIntegers.isAdic (algebraMap (Ring D w) (Carrier D w)) (inclusion_isometry D w)
    (RingHom.ker (theta D w)) (primitive D w) (kernel_power_eq_ball D w)
    (primitive_image_ne_zero D w) (by rw [primitive_norm]; norm_num)

instance plusComplete : CompleteSpace (Ring D w) :=
  (plus_isAdic D w).isPrecomplete_iff.mp inferInstance

theorem inclusion_range_eq_closedBall :
    Set.range (algebraMap (Ring D w) (Carrier D w)) = Metric.closedBall 0 1 := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right, norm_le_one_iff, valuation_le_one_iff]
  rfl

instance fieldComplete : CompleteSpace (Carrier D w) :=
  AdicNormedIntegers.fieldComplete (algebraMap (Ring D w) (Carrier D w))
    (inclusion_isometry D w) (inclusion_range_eq_closedBall D w)

theorem inclusion_range_isClosed :
    IsClosed (Set.range (algebraMap (Ring D w) (Carrier D w))) := by
  rw [inclusion_range_eq_closedBall]
  exact Metric.isClosed_closedBall

theorem cauchySeq_converges (s : ℕ → Carrier D w) (hs : CauchySeq s) :
    ∃ x : Carrier D w, Filter.Tendsto s Filter.atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hs

end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology
