import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityInverseEquation
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationBaseIdentity
import ArithmeticTeichmullerSpaces.Act1Scene1.InverseChartRawBoundary

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: the original lower function-field equivalence supplies the actual
second inverse coordinate. Its monic equation puts it in the existing lower
normalization, and the original ring map supplies the unsigned coordinate.
Every lower and unsigned infinity prime contains this coordinate.
Original proofs; no reference implementation copied.
boundary: neither maximality of `(u,v)` nor uniqueness of the normalization
fiber nor identification with the projective cusp is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityTranslationBaseField_field infinityTranslationBaseField_rationalAlgebra
  infinityTranslationBaseField_baseAlgebra infinityTranslationBaseField_baseSMul
  infinityTranslationBaseField_baseModule infinityTranslationBaseField_coefficientAlgebra
  infinityTranslationBaseField_baseTower infinityTranslationBaseField_coefficientTower
  infinityTranslationBaseRing_baseAlgebra infinityTranslationBaseRing_baseSMul
  infinityTranslationBaseRing_baseModule infinityTranslationBaseRing_coefficientAlgebra

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The actual second inverse coordinate belongs to the original lower elliptic field. -/
theorem infinityTranslation_secondCoordinate_mem_baseField :
    WeierstrassInverseChart.secondCoordinate S.prime.EK ∈
      S.infinityTranslationBaseField := by
  have h := (S.infinityTranslationBaseFunctionFieldEquiv
    (Genuine.yF S.prime.EK * (Genuine.xF S.prime.EK)⁻¹ ^ 2)).property
  change ((S.infinityTranslationBaseFunctionFieldEquiv
    (Genuine.yF S.prime.EK * (Genuine.xF S.prime.EK)⁻¹ ^ 2) :
      S.infinityTranslationBaseField) : Genuine.Ω S.prime.EK) ∈
        S.infinityTranslationBaseField at h
  rw [S.coe_infinityTranslationBaseFunctionFieldEquiv] at h
  simpa [WeierstrassInverseChart.secondCoordinate, Genuine.yG_eq, Genuine.xG_eq] using h

/-- The original first inverse coordinate in the lower normalization ring. -/
def infinityTranslationInverseFirstCoordinate : S.infinityTranslationBaseRing :=
  algebraMap S.infinityPolynomialBase S.infinityTranslationBaseRing S.infinityCoordinate

@[simp] theorem coe_infinityTranslationInverseFirstCoordinate :
    ((S.infinityTranslationInverseFirstCoordinate : S.infinityTranslationBaseField) :
      Genuine.Ω S.prime.EK) =
        WeierstrassInverseChart.firstCoordinate S.prime.EK := rfl

/-- The actual integral second inverse coordinate in the lower normalization ring. -/
def infinityTranslationInverseSecondCoordinate : S.infinityTranslationBaseRing :=
  ⟨⟨WeierstrassInverseChart.secondCoordinate S.prime.EK,
    S.infinityTranslation_secondCoordinate_mem_baseField⟩, by
    rw [mem_integralClosure_iff]
    letI : IsScalarTower S.infinityPolynomialBase S.infinityTranslationBaseField
        (Genuine.Ω S.prime.EK) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    apply (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom S.infinityPolynomialBase S.infinityTranslationBaseField
        (Genuine.Ω S.prime.EK))
      (algebraMap S.infinityTranslationBaseField (Genuine.Ω S.prime.EK)).injective).mp
    exact WeierstrassInverseChart.secondCoordinate_isIntegral S.prime.EK⟩

@[simp] theorem coe_infinityTranslationInverseSecondCoordinate :
    ((S.infinityTranslationInverseSecondCoordinate : S.infinityTranslationBaseField) :
      Genuine.Ω S.prime.EK) =
        WeierstrassInverseChart.secondCoordinate S.prime.EK := rfl

/-- The integral-closure coordinates satisfy the actual transformed equation. -/
theorem infinityTranslationInverseCoordinates_equation :
    S.infinityTranslationInverseSecondCoordinate ^ 2 =
      InverseChartRawBoundary.inverseEquationRhs
        (a₁ := algebraMap ↥S.prime.torsionField S.infinityTranslationBaseRing S.prime.EK.a₁)
        (a₂ := algebraMap ↥S.prime.torsionField S.infinityTranslationBaseRing S.prime.EK.a₂)
        (a₃ := algebraMap ↥S.prime.torsionField S.infinityTranslationBaseRing S.prime.EK.a₃)
        (a₄ := algebraMap ↥S.prime.torsionField S.infinityTranslationBaseRing S.prime.EK.a₄)
        (a₆ := algebraMap ↥S.prime.torsionField S.infinityTranslationBaseRing S.prime.EK.a₆)
        (u := S.infinityTranslationInverseFirstCoordinate)
        (v := S.infinityTranslationInverseSecondCoordinate) := by
  apply Subtype.ext
  apply Subtype.ext
  change WeierstrassInverseChart.secondCoordinate S.prime.EK ^ 2 =
    WeierstrassInverseChart.firstCoordinate S.prime.EK *
      (1 + algebraMap ↥S.prime.torsionField (Genuine.Ω S.prime.EK) S.prime.EK.a₂ *
          WeierstrassInverseChart.firstCoordinate S.prime.EK
        + algebraMap ↥S.prime.torsionField (Genuine.Ω S.prime.EK) S.prime.EK.a₄ *
          WeierstrassInverseChart.firstCoordinate S.prime.EK ^ 2
        + algebraMap ↥S.prime.torsionField (Genuine.Ω S.prime.EK) S.prime.EK.a₆ *
          WeierstrassInverseChart.firstCoordinate S.prime.EK ^ 3
        - algebraMap ↥S.prime.torsionField (Genuine.Ω S.prime.EK) S.prime.EK.a₁ *
          WeierstrassInverseChart.secondCoordinate S.prime.EK
        - algebraMap ↥S.prime.torsionField (Genuine.Ω S.prime.EK) S.prime.EK.a₃ *
          WeierstrassInverseChart.firstCoordinate S.prime.EK *
          WeierstrassInverseChart.secondCoordinate S.prime.EK)
  exact WeierstrassInverseChart.equation S.prime.EK

/-- Every actual lower infinity prime contains the first inverse coordinate. -/
theorem infinityTranslationInverseFirstCoordinate_mem_fiber
    (q : S.infinityTranslationBaseFiber) :
    S.infinityTranslationInverseFirstCoordinate ∈ q.1 := by
  change S.infinityCoordinate ∈ q.1.under S.infinityPolynomialBase
  rw [← q.2.2.over]
  exact S.infinityCoordinate_mem_baseIdeal

/-- The raw prime theorem now applies to the seed's actual lower normalization. -/
theorem infinityTranslationInverseSecondCoordinate_mem_fiber
    (q : S.infinityTranslationBaseFiber) :
    S.infinityTranslationInverseSecondCoordinate ∈ q.1 :=
  InverseChartRawBoundary.second_inverse_coordinate_mem_of_prime
    S.infinityTranslationInverseCoordinates_equation q.2.1
    (S.infinityTranslationInverseFirstCoordinate_mem_fiber q)

/-- The original lower-to-upper map supplies the actual unsigned normalization coordinate. -/
def infinityUnsignedInverseSecondCoordinate : S.infinityNormalizationRing false :=
  S.infinityTranslationRingMap S.infinityTranslationInverseSecondCoordinate

@[simp] theorem coe_infinityUnsignedInverseSecondCoordinate :
    ((S.infinityUnsignedInverseSecondCoordinate : S.infinityNormalizationField false) :
      Genuine.Ω S.prime.EK) =
        WeierstrassInverseChart.secondCoordinate S.prime.EK := rfl

/-- Every actual upper infinity prime also contains this same inverse coordinate. -/
theorem infinityUnsignedInverseSecondCoordinate_mem_fiber
    (q : S.infinityFiber false) :
    S.infinityUnsignedInverseSecondCoordinate ∈ q.1 :=
  S.infinityTranslationInverseSecondCoordinate_mem_fiber (S.infinityTranslationFiberMap q)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
