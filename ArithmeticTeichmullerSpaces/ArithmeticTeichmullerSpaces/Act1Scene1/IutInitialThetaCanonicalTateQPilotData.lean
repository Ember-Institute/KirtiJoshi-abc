import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalSourceAudit

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-TATE-QPILOT-DATA
source: the actual InitialThetaData Tate parameter family and the
`ofInitialThetaCanonicalTateData` source adapter.
fidelity: constructs the Scene1 q-pilot bundle from equality of the link's
Tate family with the actual initial-theta Tate family. This avoids requiring
an unrelated whole-link equality; analytic volume and q-family obligations
remain fields of the explicit Scene1 base.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

namespace Corollary312Scene1QPilotData

noncomputable def ofCanonicalInitialThetaTateData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hTate : base.target.scene1.data.link.tate =
      iutInitialThetaTateParameterData D)
    (hDegree : Module.finrank ℚ D.F = 1) :
    Corollary312Scene1QPilotData (K := D.F) (O := O) p := by
  let hCompat : QNormTateCompatibility base.target.scene1.data.link :=
    base.qFamily.compatibility
  let source := IutQPilotSource.ofInitialThetaCanonicalTateData
    D p hEll hTate hCompat
  have hRaw := source.toSceneQPilot_rawQNormDegreeNormalization p hCompat
  refine
    { base := base
      source := source
      sourceNormalization := ?_ }
  exact
    Corollary312QPilotNormalizationAudit.weighted_normalization_of_raw_normalization_of_finrank_eq_one
      p (source.toSceneQPilot p hCompat) source.orderCompatibility hRaw hDegree

end Corollary312Scene1QPilotData

end
end JoshiTeich.Act1Scene1
