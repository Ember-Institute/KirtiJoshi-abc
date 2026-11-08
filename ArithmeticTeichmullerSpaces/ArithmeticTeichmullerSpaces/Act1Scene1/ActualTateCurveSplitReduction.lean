import ArithmeticTeichmullerSpaces.Act1Scene1.TateCurveIntegralMinimal
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.ReductionNorm
import TateCurvesTheta.TateCurve.IntegralModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
source-id: JT-SCENE1-ACTUAL-TATE-CURVE-SPLIT-REDUCTION
source: Joshi III `ss:theta-data-fixing2` and `ss:val-sets-defn`;
locked `tate-curves-theta` Tate coefficient and invariant bounds;
Mathlib's `HasSplitMultiplicativeReduction` criterion.
fidelity: constructs the actual Tate equation over the completion's integer
ring, identifies its residue equation as the nodal cubic, and proves the
Mathlib split tangent polynomial factors over the actual residue field.
Original proof; no reference implementation copied.
boundary: Scene1/Derived. This does not descend a local coordinate change
to a global change or prove full `VBad` coverage.
-/

namespace JoshiTeich.Act1Scene1.TateReduction

open WeierstrassCurve NumberField IsLocalRing IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum
open JoshiTeich.ReferenceIut
open TateCurvesTheta

noncomputable section

variable {F : Type*} [Field F] [NumberField F]
variable (w : FinitePlace F)
variable (t : TateParameter (localCompletion w))
variable (h12 : (12 : localCompletion w) ≠ 0)

local notation "R" => w.maximalIdeal.adicCompletionIntegers F
local notation "Kc" => localCompletion w

/-- The Tate coefficient `a4` viewed in the completed integer ring. -/
def a4Integer : R :=
  ⟨t.a₄, (norm_le_one_iff_valued w _).mp t.norm_a₄_lt_one.le⟩

/-- The Tate coefficient `a6` viewed in the completed integer ring. -/
def a6Integer : R :=
  ⟨t.a₆, (norm_le_one_iff_valued w _).mp (t.norm_a₆_lt_one h12).le⟩

lemma a4Integer_mem_maximalIdeal :
    a4Integer w t ∈ IsLocalRing.maximalIdeal R := by
  change a4Integer w t ∈ (IsDiscreteValuationRing.maximalIdeal R).asIdeal
  apply (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
    (K := localCompletion w) (IsDiscreteValuationRing.maximalIdeal R) _).mp
  exact (valuation_lt_one_iff w _).mpr t.norm_a₄_lt_one

lemma a6Integer_mem_maximalIdeal :
    a6Integer w t h12 ∈ IsLocalRing.maximalIdeal R := by
  change a6Integer w t h12 ∈ (IsDiscreteValuationRing.maximalIdeal R).asIdeal
  apply (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
    (K := localCompletion w) (IsDiscreteValuationRing.maximalIdeal R) _).mp
  exact (valuation_lt_one_iff w _).mpr (t.norm_a₆_lt_one h12)

/-- The Tate equation over the actual completed integer ring. -/
def actualIntegralModel : WeierstrassCurve R :=
  ⟨1, 0, 0, a4Integer w t, a6Integer w t h12⟩

lemma actualIntegralModel_baseChange :
    (actualIntegralModel w t h12).baseChange Kc = t.tateCurve := by
  ext <;> rfl

lemma tateCurve_isIntegral (h12 : (12 : Kc) ≠ 0) : t.tateCurve.IsIntegral R :=
  ⟨actualIntegralModel w t h12, (actualIntegralModel_baseChange w t h12).symm⟩

lemma tateCurve_isMinimal (h12 : (12 : Kc) ≠ 0) : t.tateCurve.IsMinimal R := by
  letI : t.tateCurve.IsIntegral R := tateCurve_isIntegral w t h12
  apply isMinimal_of_integral_c₄_unit t.tateCurve
  exact (valuation_eq_one_iff w _).mpr t.norm_c₄_eq_one

lemma tateCurve_hasMultiplicativeReduction (h12 : (12 : Kc) ≠ 0) :
    t.tateCurve.HasMultiplicativeReduction R := by
  refine {
    toIsMinimal := tateCurve_isMinimal w t h12
    badReduction := (valuation_lt_one_iff w _).mpr (t.norm_Δ_lt_one h12)
    multiplicativeReduction := (valuation_eq_one_iff w _).mpr t.norm_c₄_eq_one }

lemma tateCurve_integralModel_eq_actual :
    letI : t.tateCurve.IsIntegral R := tateCurve_isIntegral w t h12
    t.tateCurve.integralModel R = actualIntegralModel w t h12 := by
  letI : t.tateCurve.IsIntegral R := tateCurve_isIntegral w t h12
  apply WeierstrassCurve.map_injective (IsFractionRing.injective R Kc)
  change (t.tateCurve.integralModel R).baseChange Kc =
    (actualIntegralModel w t h12).baseChange Kc
  rw [baseChange_integralModel_eq, actualIntegralModel_baseChange]

lemma actualIntegralModel_reduction :
    (actualIntegralModel w t h12).map (algebraMap R (ResidueField R)) =
      (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve (ResidueField R)) := by
  have ha₄ : algebraMap R (ResidueField R) (a4Integer w t) = 0 := by
    rw [ResidueField.algebraMap_eq, residue_eq_zero_iff]
    exact a4Integer_mem_maximalIdeal w t
  have ha₆ : algebraMap R (ResidueField R) (a6Integer w t h12) = 0 := by
    rw [ResidueField.algebraMap_eq, residue_eq_zero_iff]
    exact a6Integer_mem_maximalIdeal w t h12
  ext <;> simp only [WeierstrassCurve.map, actualIntegralModel, map_one, map_zero,
    ha₄, ha₆]

/-- The actual Tate equation has split multiplicative reduction over `O_w`. -/
lemma tateCurve_hasSplitMultiplicativeReduction (h12 : (12 : Kc) ≠ 0) :
    t.tateCurve.HasSplitMultiplicativeReduction R := by
  letI : t.tateCurve.IsIntegral R := tateCurve_isIntegral w t h12
  have hred : (t.tateCurve.integralModel R).map (algebraMap R (ResidueField R)) =
      (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve (ResidueField R)) := by
    rw [tateCurve_integralModel_eq_actual w t h12]
    exact actualIntegralModel_reduction w t h12
  let I := t.tateCurve.integralModel R
  let r : R →+* ResidueField R := algebraMap R (ResidueField R)
  have ha₁ : r I.a₁ = 1 := by
    simpa only [WeierstrassCurve.map_a₁] using congrArg WeierstrassCurve.a₁ hred
  have ha₂ : r I.a₂ = 0 := by
    simpa only [WeierstrassCurve.map_a₂] using congrArg WeierstrassCurve.a₂ hred
  have hb₂ : r I.b₂ = 1 := by
    rw [← WeierstrassCurve.map_b₂, hred]
    norm_num [WeierstrassCurve.b₂]
  have hb₄ : r I.b₄ = 0 := by
    rw [← WeierstrassCurve.map_b₄, hred]
    norm_num [WeierstrassCurve.b₄]
  have hb₆ : r I.b₆ = 0 := by
    rw [← WeierstrassCurve.map_b₆, hred]
    norm_num [WeierstrassCurve.b₆]
  have hc₄ : r I.c₄ = 1 := by
    rw [← WeierstrassCurve.map_c₄, hred]
    norm_num [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  refine {
    toHasMultiplicativeReduction := tateCurve_hasMultiplicativeReduction w t h12
    splitMultiplicativeReduction := ?_ }
  change Polynomial.Splits ((Polynomial.C I.c₄ * Polynomial.X ^ 2 +
    Polynomial.C (I.a₁ * I.c₄) * Polynomial.X -
    Polynomial.C (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)).map r)
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    map_mul, map_add, map_sub, map_ofNat, ha₁, ha₂, hb₂, hb₄, hb₆, hc₄,
    zero_mul, mul_zero, one_mul, zero_sub, sub_zero, add_zero,
    Polynomial.C_0, Polynomial.C_1]
  convert (Polynomial.Splits.X.mul
    (Polynomial.Splits.X_add_C (1 : ResidueField R))) using 1 <;>
    simp only [Polynomial.C_1, mul_one] <;> ring

end
end JoshiTeich.Act1Scene1.TateReduction
