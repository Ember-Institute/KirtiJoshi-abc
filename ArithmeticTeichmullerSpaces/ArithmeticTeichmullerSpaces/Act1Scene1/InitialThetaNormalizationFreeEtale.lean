import ArithmeticTeichmullerSpaces.Act1Scene1.EtaleOpenRestriction
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaEtaleNeighborhoodSchemes

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's universal property of open immersions and etale source locality.
fidelity: constructs the actual free open subscheme, lifts the proved affine
neighborhoods into it, and packages them as a formal scheme open cover. The
restriction of the original signed normalization map is etale. Neighborhood
charts retain their existing maps and satisfy the open-immersion pullback law.
boundary: Scene1/Derived. This is the ordinary normalization map on its free
open part; the orbicurve realization and its global etale/cartesian comparison remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry
open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] coverEtaleNeighborhoodInclusion_isOpenImmersion
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The proved free locus as an actual open subset of the normalization scheme. -/
def coverNormalizationFreeOpen : (S.coverNormalizationScheme false).Opens :=
  EtaleOpenRestriction.specOpen (R := S.coverNormalizationRing false)
    ⟨S.coverNormalizationFreeGeometricLocus, S.coverNormalizationFreeGeometricLocus_isOpen⟩

def coverNormalizationFreeScheme : Scheme := S.coverNormalizationFreeOpen.toScheme

def coverNormalizationFreeInclusion :
    S.coverNormalizationFreeScheme ⟶ S.coverNormalizationScheme false :=
  S.coverNormalizationFreeOpen.ι

theorem coverNormalizationFreeInclusion_isOpenImmersion :
    IsOpenImmersion S.coverNormalizationFreeInclusion :=
  inferInstanceAs (IsOpenImmersion S.coverNormalizationFreeOpen.ι)

/-- The restriction of the existing signed normalization map to the free open part. -/
def coverNormalizationFreeMap :
    S.coverNormalizationFreeScheme ⟶ S.coverNormalizationScheme true :=
  S.coverNormalizationFreeInclusion ≫ S.signedCoverNormalizationMap

theorem coverEtaleNeighborhood_range_subset_freeOpen
    (i : S.coverNormalizationFreeGeometricLocus) :
    Set.range (S.coverEtaleNeighborhoodInclusion i) ⊆ S.coverNormalizationFreeOpen := by
  intro y hy
  exact S.coverEtaleNeighborhoodInclusion_range_subset_free i hy

theorem coverEtaleNeighborhood_covers_freeOpen (z : S.coverNormalizationFreeOpen) :
    ∃ i : S.coverNormalizationFreeGeometricLocus,
      z.val ∈ Set.range (S.coverEtaleNeighborhoodInclusion i) := by
  let i : S.coverNormalizationFreeGeometricLocus := ⟨z.val, z.property⟩
  exact ⟨i, S.coverEtaleNeighborhood_contains_point i⟩

/-- The actual scheme-theoretic open cover, with the proved neighborhoods as charts. -/
def coverNormalizationFreeOpenCover : S.coverNormalizationFreeScheme.OpenCover :=
  EtaleOpenRestriction.openCover S.coverNormalizationFreeOpen
    S.coverEtaleNeighborhoodScheme S.coverEtaleNeighborhoodInclusion
    S.coverEtaleNeighborhood_range_subset_freeOpen S.coverEtaleNeighborhood_covers_freeOpen

theorem coverNormalizationFreeOpenCover_chart_comp
    (i : S.coverNormalizationFreeGeometricLocus) :
    S.coverNormalizationFreeOpenCover.f i ≫ S.coverNormalizationFreeMap =
      S.coverEtaleNeighborhoodMap i :=
  (EtaleOpenRestriction.liftToOpen_comp S.coverNormalizationFreeOpen
    S.coverEtaleNeighborhoodScheme S.coverEtaleNeighborhoodInclusion
    S.coverEtaleNeighborhood_range_subset_freeOpen S.signedCoverNormalizationMap i).trans
      (S.coverEtaleNeighborhood_triangle i)

theorem coverNormalizationFreeOpenCover_chart_isPullback
    (i : S.coverNormalizationFreeGeometricLocus) :
    CategoryTheory.IsPullback (S.coverNormalizationFreeOpenCover.f i)
      (𝟙 (S.coverEtaleNeighborhoodScheme i)) S.coverNormalizationFreeInclusion
        (S.coverEtaleNeighborhoodInclusion i) :=
  EtaleOpenRestriction.liftToOpen_isPullback S.coverNormalizationFreeOpen
    S.coverEtaleNeighborhoodScheme S.coverEtaleNeighborhoodInclusion
    S.coverEtaleNeighborhood_range_subset_freeOpen i

/-- Etaleness now holds for the full ordinary free-open restriction. -/
theorem coverNormalizationFreeMap_etale : Etale S.coverNormalizationFreeMap :=
  EtaleOpenRestriction.restriction_etale S.coverNormalizationFreeOpen
    S.coverEtaleNeighborhoodScheme S.coverEtaleNeighborhoodInclusion
    S.coverEtaleNeighborhood_range_subset_freeOpen S.coverEtaleNeighborhood_covers_freeOpen
    S.signedCoverNormalizationMap (fun i =>
      (S.coverEtaleNeighborhood_triangle i).symm ▸ S.coverEtaleNeighborhoodMap_etale i)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
