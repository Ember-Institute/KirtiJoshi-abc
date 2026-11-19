import Definitions.Def_TripodCanonicalHighHeightComposition
import Definitions.Def_TripodStatementIIComposition
import Solutions.Source_TripodCanonicalCorollary22PrimeEstimates
import Solutions.Source_TripodProviderLegendreComparison
import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness
import Theorems.Thm_AbcAdaptation_Tripod_epsilonELargeHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- Corollary 2.3 for the tripod from Corollary 3.12 on the source (P7) bundles. -/
theorem statementII_of_explicitPrimeEstimates_on_sourceP7
    (P : CurveProviders)
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (anab : AnabelianExistence AG TG)
    (h312 : ∀ (K : CompactlyBounded) (d : ℕ) (X : Corollary312VariantData.{0, 0} AG TG),
      let CF : CurveFactsProp P K d
          (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K d⟩
      let CI := curveInputs_from_source P K d CF (hcore K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)
      IsSourceP7Variant CI anab X → Corollary312Variant X) :
    StatementII :=
  statementII_of_children boundedDegreeFiniteness
    (highHeightEstimate_of_canonical_children
      (canonicalLegendreHeightComparison_of_provider P)
      (canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates_on_sourceP7
        P hcore anab h312)
      epsilonELargeHeight)

end AbcAdaptation.Tripod
