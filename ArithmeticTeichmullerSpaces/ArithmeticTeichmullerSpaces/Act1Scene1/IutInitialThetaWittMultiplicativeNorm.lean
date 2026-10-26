import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedMultiplicativity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-MULTIPLICATIVE-NORM
source: Joshi II `se:ff-rings`, the multiplicative rho norms defining
the Frechet period ring before `pr:teichmuller-lift-A/B`.
fidelity: actual bounded expansions supply the hypotheses of the proved
Witt Gauss multiplication theorem. The same p-power presentations descend
that equality to the original localization. Density and continuity give
multiplicative norms on the existing radius completions, and multiplicative
coordinate seminorms on the existing common ring. No norms are replaced.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the paper B identity and period/BK comparisons
remain separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittMultiplicativeNorm

open JoshiTeich.Prologue
open InitialThetaBoundedWittExpansion
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem value_mul (ρ : InitialThetaWittRhoCompletion.Radius)
    (x y : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoValue.value D w ρ.val (x * y) =
      InitialThetaWittRhoValue.value D w ρ.val x * InitialThetaWittRhoValue.value D w ρ.val y := by
  obtain ⟨m, a, c, C, _, hC, hca, ha⟩ := hasBoundedExpansion D w x
  obtain ⟨n, b, d, E, _, hE, hdb, hb⟩ := hasBoundedExpansion D w y
  have hρtop : ρ.val ≠ ⊤ := (ρ.property.2.trans ENNReal.one_lt_top).ne
  have he : toAmbient D w (x * y) * (Arithmetic.residueChar w.1 : Ambient D w) ^ (m + n) =
      algebraMap (FieldWitt D w) (Ambient D w) (a * b) := by
    rw [map_mul, map_mul, pow_add]
    calc
      _ = (toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m) *
          (toAmbient D w y * (Arithmetic.residueChar w.1 : Ambient D w) ^ n) :=
        mul_mul_mul_comm _ _ _ _
      _ = _ := by rw [ha, hb]
  have haBound : ∀ k, ‖WittTeichmullerExpansion.digits (Arithmetic.residueChar w.1) a k‖ ≤ C := by
    intro k
    rw [← congrFun (WittTeichmullerExpansion.digits_unique (Arithmetic.residueChar w.1) a c hca) k]
    exact hC k
  have hbBound : ∀ k, ‖WittTeichmullerExpansion.digits (Arithmetic.residueChar w.1) b k‖ ≤ E := by
    intro k
    rw [← congrFun (WittTeichmullerExpansion.digits_unique (Arithmetic.residueChar w.1) b d hdb) k]
    exact hE k
  rw [InitialThetaWittRhoValue.value_eq_of_presentation D w ρ.val ρ.property.1.ne' hρtop _
      (m + n) (a * b) he,
    InitialThetaWittRhoValue.value_eq_of_presentation D w ρ.val ρ.property.1.ne' hρtop x m a ha,
    InitialThetaWittRhoValue.value_eq_of_presentation D w ρ.val ρ.property.1.ne' hρtop y n b hb,
    WittWeightedMultiplicativity.value_mul (Arithmetic.residueChar w.1)
      (LocalGeometricFontaine.integerRing (InitialThetaTiltField.Carrier D w))
      (LocalGeometricFontaine.mem_integerRing (InitialThetaTiltField.Carrier D w))
      ρ.val ρ.property.1.ne' ρ.property.2 a b C E haBound hbBound]
  simp only [div_eq_mul_inv, ENNReal.inv_pow]
  rw [pow_add]
  exact mul_mul_mul_comm
    (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ.val a)
    (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ.val b)
    ((ρ.val⁻¹) ^ m) ((ρ.val⁻¹) ^ n)

theorem realValue_mul (ρ : InitialThetaWittRhoCompletion.Radius)
    (x y : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoNorm.realValue D w ρ.val (x * y) =
      InitialThetaWittRhoNorm.realValue D w ρ.val x * InitialThetaWittRhoNorm.realValue D w ρ.val y := by
  exact (congrArg ENNReal.toReal (value_mul D w ρ x y)).trans (ENNReal.toReal_mul)

def mulRingNorm (ρ : InitialThetaWittRhoCompletion.Radius) :
    MulRingNorm (InitialThetaBoundedWittLocalization.Ring D w) where
  __ := (InitialThetaWittRhoNorm.ringNorm D w ρ.val ρ.property.1.ne' ρ.property.2.le).toAddGroupNorm
  map_one' := InitialThetaWittRhoNorm.realValue_one D w ρ.val ρ.property.1.ne' ρ.property.2.le
  map_mul' := realValue_mul D w ρ

instance sourceNormMul (ρ : InitialThetaWittRhoCompletion.Radius) :
    NormMulClass (InitialThetaWittRhoCompletion.Source D w ρ) where
  norm_mul x y := realValue_mul D w ρ x y

instance completedNormMul (ρ : InitialThetaWittRhoCompletion.Radius) :
    NormMulClass (InitialThetaWittRhoCompletion.Completed D w ρ) where
  norm_mul x y := by
    refine (InitialThetaWittRhoCompletion.inclusion_denseRange D w ρ).induction_on₂
      (p := fun a b : InitialThetaWittRhoCompletion.Completed D w ρ => ‖a * b‖ = ‖a‖ * ‖b‖)
      ?_ ?_ x y
    · exact isClosed_eq (continuous_fst.mul continuous_snd).norm (continuous_fst.norm.mul continuous_snd.norm)
    · intro a b
      rw [← map_mul, InitialThetaWittRhoCompletion.inclusion_norm,
        InitialThetaWittRhoCompletion.inclusion_norm, InitialThetaWittRhoCompletion.inclusion_norm]
      exact realValue_mul D w ρ a b

theorem coordinateSeminorm_mul (ρ : InitialThetaWittRhoCompletion.Radius)
    (x y : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (x * y) =
      InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x *
        InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ y := by
  change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (x * y)‖ =
    ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ * ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ y‖
  rw [map_mul, norm_mul]

def coordinateMulSeminorm (ρ : InitialThetaWittRhoCompletion.Radius) :
    MulRingSeminorm (InitialThetaWittAllRadiusCompletion.Carrier D w) where
  __ := (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ).toAddGroupSeminorm
  map_one' := by
    change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ 1‖ = 1
    rw [map_one]
    have h := InitialThetaWittRhoCompletion.inclusion_norm D w ρ 1
    rw [map_one] at h
    exact h.trans (InitialThetaWittRhoNorm.realValue_one D w ρ.val ρ.property.1.ne' ρ.property.2.le)
  map_mul' := coordinateSeminorm_mul D w ρ

end
end JoshiTeich.Act1Scene1.InitialThetaWittMultiplicativeNorm
