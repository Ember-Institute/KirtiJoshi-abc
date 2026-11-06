import ArithmeticTeichmullerSpaces.Act1Scene1.FiniteEtaleRankOneIso
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationTensorDomain
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaUnbranchedNormalizationComparison
import Mathlib.AlgebraicGeometry.Properties

/-!
source-id: JT-SCENE1-INITIAL-THETA-UNBRANCHED-NORMALIZATION-ISO
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the original two-torsion branch complement, finite normalization and
local constancy of finite etale rank.
fidelity: the canonical unsigned normalization comparison is an isomorphism
over the specified branch complement. The resulting square uses the original
signed normalization and unsigned base maps restricted to the same source.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived. This proves the ordinary Cartesian covering square
on the original branch complement. Behavior over the branch, orbicurve/root
stack realization, core, cusp and the full geometry producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] coverTensorBaseAlgebra coverTensorBaseSMul coverTensorBaseModule
  baseTensorBaseAlgebra baseTensorBaseSMul baseTensorBaseModule
  normalizationTensorCommRing tensorRingBaseAlgebra normalizationTensorBase_xLineSMul
  normalizationFieldTensorBaseAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem normalizationTensorUnbranchedOpen_nonempty :
    (S.normalizationTensorUnbranchedOpen : Set S.normalizationTensorScheme).Nonempty := by
  obtain ⟨x, hx⟩ := S.signedCoverUnbranchedOpen_nonempty
  obtain ⟨y, _⟩ := S.tensorToSignedCoverUnbranchedMap.surjective ⟨x, hx⟩
  exact ⟨y.val, y.property⟩

instance integral_normalizationTensorScheme : IsIntegral S.normalizationTensorScheme := by
  unfold normalizationTensorScheme
  infer_instance

theorem normalizationToTensorScheme_exists_iso_basicOpen :
    ∃ d : S.normalizationTensorRing, d ≠ 0 ∧
      IsIso (S.normalizationToTensorScheme ∣_ PrimeSpectrum.basicOpen d) := by
  let T := S.normalizationTensorRing
  let B := S.coverNormalizationRing false
  let N := Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false
  letI : Algebra T B := S.normalizationTensorMap.toRingHom.toAlgebra
  letI : Algebra T N := S.normalizationTensorFieldAlgebra
  letI : IsScalarTower T B N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing T N := S.normalizationTensor_fractionField
  haveI : Module.Finite T B := S.normalizationTensorMap_finite
  exact finite_extension_exists_basicOpen_iso (R := T) (A := B) (K := N) Subtype.val_injective

instance isIso_normalizationUnbranchedComparison : IsIso S.normalizationUnbranchedComparison := by
  obtain ⟨d, hd, hiso⟩ := S.normalizationToTensorScheme_exists_iso_basicOpen
  let W : S.normalizationTensorScheme.Opens := PrimeSpectrum.basicOpen d
  have hW : Dense (W : Set S.normalizationTensorScheme) := by
    apply W.isOpen.dense
    refine ⟨(⊥ : PrimeSpectrum S.normalizationTensorRing), ?_⟩
    exact hd
  have : IsIso (S.normalizationToTensorScheme ∣_ W) := hiso
  have : Etale (S.normalizationToTensorScheme ∣_ S.normalizationTensorUnbranchedOpen) :=
    S.etale_normalizationUnbranchedComparison
  have : IsFinite (S.normalizationToTensorScheme ∣_ S.normalizationTensorUnbranchedOpen) :=
    S.finite_normalizationUnbranchedComparison
  exact finiteFlat_isIso_restrict_of_dense_isIso_restrict S.normalizationToTensorScheme
    W S.normalizationTensorUnbranchedOpen hW S.normalizationTensorUnbranchedOpen_nonempty

theorem normalizationUnbranchedSourceOpen_le_signedCover :
    S.normalizationUnbranchedSourceOpen ≤
      S.signedCoverNormalizationMap ⁻¹ᵁ S.signedCoverUnbranchedOpen := by
  change S.normalizationToTensorScheme ⁻¹ᵁ S.normalizationTensorUnbranchedOpen ≤ _
  rw [← S.normalizationToTensorScheme_comp_left, Scheme.Hom.comp_preimage]
  exact S.normalizationToTensorScheme.preimage_mono inf_le_left

theorem normalizationUnbranchedComparison_comp_signedCover :
    S.normalizationUnbranchedComparison ≫ S.tensorToSignedCoverUnbranchedMap =
      S.signedCoverNormalizationMap.resLE S.signedCoverUnbranchedOpen
        S.normalizationUnbranchedSourceOpen S.normalizationUnbranchedSourceOpen_le_signedCover := by
  have hg : S.tensorToSignedCoverUnbranchedMap ≫ S.signedCoverUnbranchedOpen.ι =
      S.normalizationTensorUnbranchedOpen.ι ≫ S.normalizationTensorToSignedCover :=
    Scheme.Hom.resLE_comp_ι S.normalizationTensorToSignedCover inf_le_left
  have he : S.normalizationToTensorScheme ⁻¹ᵁ S.normalizationTensorUnbranchedOpen ≤
      S.signedCoverNormalizationMap ⁻¹ᵁ S.signedCoverUnbranchedOpen :=
    S.normalizationUnbranchedSourceOpen_le_signedCover
  change (S.normalizationToTensorScheme ∣_ S.normalizationTensorUnbranchedOpen) ≫
      S.tensorToSignedCoverUnbranchedMap =
    S.signedCoverNormalizationMap.resLE S.signedCoverUnbranchedOpen
      (S.normalizationToTensorScheme ⁻¹ᵁ S.normalizationTensorUnbranchedOpen) he
  rw [← cancel_mono S.signedCoverUnbranchedOpen.ι]
  rw [Category.assoc, hg, ← Category.assoc, morphismRestrict_ι,
    Category.assoc, S.normalizationToTensorScheme_comp_left, Scheme.Hom.resLE_comp_ι]

def unsignedNormalizationUnbranchedToSignedCover :
    S.normalizationUnbranchedSourceOpen.toScheme ⟶ S.signedCoverUnbranchedOpen.toScheme :=
  S.signedCoverNormalizationMap.resLE S.signedCoverUnbranchedOpen
    S.normalizationUnbranchedSourceOpen S.normalizationUnbranchedSourceOpen_le_signedCover

def unsignedNormalizationUnbranchedToBase :
    S.normalizationUnbranchedSourceOpen.toScheme ⟶ S.baseUnsignedUnbranchedOpen.toScheme :=
  (S.coverToBaseNormalizationMap false).resLE S.baseUnsignedUnbranchedOpen
    S.normalizationUnbranchedSourceOpen S.normalizationUnbranchedSourceOpen_eq.le

theorem unsignedNormalizationUnbranchedSquare_isPullback :
    IsPullback S.unsignedNormalizationUnbranchedToSignedCover S.unsignedNormalizationUnbranchedToBase
      S.signedCoverUnbranchedMap S.signedBaseUnbranchedMap := by
  dsimp only [unsignedNormalizationUnbranchedToSignedCover, unsignedNormalizationUnbranchedToBase]
  rw [← S.normalizationUnbranchedComparison_comp_signedCover,
    ← S.normalizationUnbranchedComparison_comp_unsignedBase]
  refine S.normalizationTensorUnbranchedSquare_isPullback.of_iso'
    (asIso S.normalizationUnbranchedComparison) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  all_goals simp

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
