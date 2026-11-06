import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaUnbranchedComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaUnsignedNormalizationEtale

/-!
source-id: JT-SCENE1-INITIAL-THETA-UNBRANCHED-NORMALIZATION-COMPARISON
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual normalization square and original two-torsion branch complement.
fidelity: restricts the original unsigned normalization comparison to the
tensor branch complement. Its source is exactly the unsigned covering above
the same base open, and its original base projection is preserved. The
comparison is finite etale, using the established unsigned etale cover and
the tensor projection's etaleness.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived. This proves the canonical comparison finite etale
on the specified open. It does not provide the global orbicurve realization,
root-stack comparison, core, cusp or full geometry producer.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

def normalizationUnbranchedSourceOpen : (S.coverNormalizationScheme false).Opens :=
  S.normalizationToTensorScheme ⁻¹ᵁ S.normalizationTensorUnbranchedOpen

theorem normalizationUnbranchedSourceOpen_eq :
    S.normalizationUnbranchedSourceOpen =
      S.coverToBaseNormalizationMap false ⁻¹ᵁ S.baseUnsignedUnbranchedOpen := by
  have hleft :
      S.signedCoverNormalizationMap ⁻¹ᵁ S.signedCoverUnbranchedOpen =
        S.coverToBaseNormalizationMap false ⁻¹ᵁ S.baseUnsignedUnbranchedOpen := by
    change (S.signedCoverNormalizationMap ≫ S.coverToBaseNormalizationMap true) ⁻¹ᵁ
        S.baseNormalizationUnbranchedOpen =
      (S.coverToBaseNormalizationMap false ≫ S.signedBaseNormalizationMap) ⁻¹ᵁ
        S.baseNormalizationUnbranchedOpen
    rw [S.normalizationMap_square]
  change S.normalizationToTensorScheme ⁻¹ᵁ
    (S.normalizationTensorToSignedCover ⁻¹ᵁ S.signedCoverUnbranchedOpen ⊓
      S.normalizationTensorToUnsignedBase ⁻¹ᵁ S.baseUnsignedUnbranchedOpen) = _
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    S.normalizationToTensorScheme_comp_left, ← Scheme.Hom.comp_preimage,
    S.normalizationToTensorScheme_comp_right, hleft, inf_idem]

def normalizationUnbranchedComparison : S.normalizationUnbranchedSourceOpen.toScheme ⟶
    S.normalizationTensorUnbranchedOpen.toScheme :=
  S.normalizationToTensorScheme ∣_ S.normalizationTensorUnbranchedOpen

theorem normalizationUnbranchedComparison_comp_unsignedBase :
    S.normalizationUnbranchedComparison ≫ S.tensorToUnsignedBaseUnbranchedMap =
      (S.coverToBaseNormalizationMap false).resLE S.baseUnsignedUnbranchedOpen
        S.normalizationUnbranchedSourceOpen S.normalizationUnbranchedSourceOpen_eq.le := by
  have hg : S.tensorToUnsignedBaseUnbranchedMap ≫ S.baseUnsignedUnbranchedOpen.ι =
      S.normalizationTensorUnbranchedOpen.ι ≫ S.normalizationTensorToUnsignedBase :=
    Scheme.Hom.resLE_comp_ι S.normalizationTensorToUnsignedBase inf_le_right
  have he : S.normalizationToTensorScheme ⁻¹ᵁ S.normalizationTensorUnbranchedOpen ≤
      S.coverToBaseNormalizationMap false ⁻¹ᵁ S.baseUnsignedUnbranchedOpen :=
    S.normalizationUnbranchedSourceOpen_eq.le
  change (S.normalizationToTensorScheme ∣_ S.normalizationTensorUnbranchedOpen) ≫
      S.tensorToUnsignedBaseUnbranchedMap =
    (S.coverToBaseNormalizationMap false).resLE S.baseUnsignedUnbranchedOpen
      (S.normalizationToTensorScheme ⁻¹ᵁ S.normalizationTensorUnbranchedOpen) he
  rw [← cancel_mono S.baseUnsignedUnbranchedOpen.ι]
  rw [Category.assoc, hg, ← Category.assoc, morphismRestrict_ι,
    Category.assoc, S.normalizationToTensorScheme_comp_right,
    Scheme.Hom.resLE_comp_ι]

instance finite_normalizationUnbranchedComparison : IsFinite S.normalizationUnbranchedComparison :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict S.normalizationToTensorScheme
      S.normalizationTensorUnbranchedOpen).flip S.finite_normalizationToTensorScheme

instance etale_normalizationUnbranchedComparison : Etale S.normalizationUnbranchedComparison := by
  have : Etale
      (S.normalizationUnbranchedComparison ≫ S.tensorToUnsignedBaseUnbranchedMap) := by
    rw [S.normalizationUnbranchedComparison_comp_unsignedBase]
    infer_instance
  exact Etale.of_comp S.normalizationUnbranchedComparison S.tensorToUnsignedBaseUnbranchedMap

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
