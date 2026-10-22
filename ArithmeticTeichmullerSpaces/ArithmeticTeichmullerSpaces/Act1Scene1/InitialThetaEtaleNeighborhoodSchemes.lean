import ArithmeticTeichmullerSpaces.Act1Scene1.AffineEtaleNeighborhood
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedEtale

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
actual localization open immersions and the proved normalization etale locus.
fidelity: every free prime of the actual unsigned normalization supplies an
affine scheme, an open immersion into that normalization and an etale map to
the signed normalization. The triangle with the existing covering commutes.
The neighborhood images lie in, and together cover, the free locus.
boundary: Scene1/Derived. This is the ordinary etale part of the normalization
cover; orbicurve realization and orbicurve cartesian/etale comparison remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry
open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] signedCoverNormalizationAlgebra signedCoverNormalizationGaloisAction
  coverNormalizationPointAction coverNormalizationAwayAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance neighborhoodPresentation :
    Algebra.FinitePresentation (S.coverNormalizationRing true) (S.coverNormalizationRing false) :=
  Genuine.etaleNormPresentation S.prime.EK S.prime.ℓ S.prime.M

/-- Use the proved neighborhood data at the actual free prime and its contraction. -/
def coverEtaleNeighborhoodData (x : S.coverNormalizationFreeGeometricLocus) :
    {f : S.coverNormalizationRing false //
      f ∉ x.val.asIdeal ∧ Algebra.Etale (S.coverNormalizationRing true) (Localization.Away f)} :=
  S.coverNormalizationEtaleNeighborhood
    (x.val.asIdeal.under (S.coverNormalizationRing true)) x.val.asIdeal x.property

def coverEtaleNeighborhoodScheme (x : S.coverNormalizationFreeGeometricLocus) : Scheme :=
  AffineEtaleNeighborhood.scheme (S.coverEtaleNeighborhoodData x).val

/-- The actual open immersion from the chosen neighborhood. -/
def coverEtaleNeighborhoodInclusion (x : S.coverNormalizationFreeGeometricLocus) :
    S.coverEtaleNeighborhoodScheme x ⟶ S.coverNormalizationScheme false :=
  AffineEtaleNeighborhood.inclusion (S.coverEtaleNeighborhoodData x).val

/-- The actual map from the neighborhood to the signed normalization. -/
def coverEtaleNeighborhoodMap (x : S.coverNormalizationFreeGeometricLocus) :
    S.coverEtaleNeighborhoodScheme x ⟶ S.coverNormalizationScheme true :=
  AffineEtaleNeighborhood.toBase (R := S.coverNormalizationRing true)
    (S.coverEtaleNeighborhoodData x).val

theorem coverEtaleNeighborhoodInclusion_isOpenImmersion
    (x : S.coverNormalizationFreeGeometricLocus) :
    IsOpenImmersion (S.coverEtaleNeighborhoodInclusion x) :=
  AffineEtaleNeighborhood.inclusion_isOpenImmersion (S.coverEtaleNeighborhoodData x).val

attribute [local instance] coverEtaleNeighborhoodInclusion_isOpenImmersion

theorem coverEtaleNeighborhoodMap_etale (x : S.coverNormalizationFreeGeometricLocus) :
    Etale (S.coverEtaleNeighborhoodMap x) := by
  have : Algebra.Etale (S.coverNormalizationRing true)
      (Localization.Away (S.coverEtaleNeighborhoodData x).val) :=
    (S.coverEtaleNeighborhoodData x).property.2
  exact AffineEtaleNeighborhood.toBase_etale (R := S.coverNormalizationRing true)
    (S.coverEtaleNeighborhoodData x).val

theorem coverEtaleNeighborhood_triangle (x : S.coverNormalizationFreeGeometricLocus) :
    S.coverEtaleNeighborhoodInclusion x ≫ S.signedCoverNormalizationMap =
      S.coverEtaleNeighborhoodMap x :=
  AffineEtaleNeighborhood.triangle (R := S.coverNormalizationRing true)
    (S.coverEtaleNeighborhoodData x).val

theorem coverEtaleNeighborhoodInclusion_opensRange
    (x : S.coverNormalizationFreeGeometricLocus) :
    (S.coverEtaleNeighborhoodInclusion x).opensRange =
      PrimeSpectrum.basicOpen (S.coverEtaleNeighborhoodData x).val :=
  AffineEtaleNeighborhood.inclusion_opensRange (S.coverEtaleNeighborhoodData x).val

/-- The same actual open range, presented on the unsigned prime spectrum. -/
def coverEtaleNeighborhoodRange (x : S.coverNormalizationFreeGeometricLocus) :
    TopologicalSpace.Opens (PrimeSpectrum (S.coverNormalizationRing false)) :=
  (S.coverEtaleNeighborhoodInclusion x).opensRange

theorem coverEtaleNeighborhoodRange_eq_basicOpen (x : S.coverNormalizationFreeGeometricLocus) :
    S.coverEtaleNeighborhoodRange x = PrimeSpectrum.basicOpen (S.coverEtaleNeighborhoodData x).val :=
  S.coverEtaleNeighborhoodInclusion_opensRange x

theorem coverEtaleNeighborhood_contains_point (x : S.coverNormalizationFreeGeometricLocus) :
    x.val ∈ S.coverEtaleNeighborhoodRange x :=
  Eq.mpr (congrArg (fun U : TopologicalSpace.Opens
    (PrimeSpectrum (S.coverNormalizationRing false)) => x.val ∈ U)
      (S.coverEtaleNeighborhoodRange_eq_basicOpen x))
    ((PrimeSpectrum.mem_basicOpen _ _).mpr (S.coverEtaleNeighborhoodData x).property.1)

theorem coverEtaleNeighborhoodInclusion_range_subset_free
    (x : S.coverNormalizationFreeGeometricLocus) :
    (S.coverEtaleNeighborhoodRange x : Set (PrimeSpectrum (S.coverNormalizationRing false))) ⊆
      S.coverNormalizationFreeGeometricLocus := by
  have hb : (PrimeSpectrum.basicOpen (S.coverEtaleNeighborhoodData x).val :
      Set (PrimeSpectrum (S.coverNormalizationRing false))) ⊆
      Algebra.etaleLocus (S.coverNormalizationRing true) (S.coverNormalizationRing false) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr (S.coverEtaleNeighborhoodData x).property.2
  intro y hy
  exact Eq.mpr (congrArg (fun U : Set (PrimeSpectrum (S.coverNormalizationRing false)) => y ∈ U)
    S.coverNormalizationFreeGeometricLocus_eq_etaleLocus)
      (hb (Eq.mp (congrArg (fun U : TopologicalSpace.Opens
        (PrimeSpectrum (S.coverNormalizationRing false)) => y ∈ U)
          (S.coverEtaleNeighborhoodRange_eq_basicOpen x)) hy))

private theorem indexed_neighborhoods_cover {X : Type*} (U : Set X) (V : U → Set X)
    (hsub : ∀ x, V x ⊆ U) (hmem : ∀ x, x.val ∈ V x) : (⋃ x, V x) = U := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset hsub
  · intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hmem ⟨y, hy⟩⟩

/-- These actual open neighborhood images cover exactly the free locus. -/
theorem coverEtaleNeighborhoodInclusion_ranges_eq_free :
    (⋃ x : S.coverNormalizationFreeGeometricLocus,
      (S.coverEtaleNeighborhoodRange x : Set (PrimeSpectrum (S.coverNormalizationRing false)))) =
        S.coverNormalizationFreeGeometricLocus :=
  indexed_neighborhoods_cover S.coverNormalizationFreeGeometricLocus
    (fun x => (S.coverEtaleNeighborhoodRange x : Set (PrimeSpectrum (S.coverNormalizationRing false))))
    S.coverEtaleNeighborhoodInclusion_range_subset_free S.coverEtaleNeighborhood_contains_point

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
