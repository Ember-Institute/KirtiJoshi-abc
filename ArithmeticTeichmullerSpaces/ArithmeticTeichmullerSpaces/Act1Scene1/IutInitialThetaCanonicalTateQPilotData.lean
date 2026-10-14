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

theorem IutQPilotSource.qOrder_eq_initialTheta_qOrder_ofCanonicalTateData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    (hEll : T.ell = D.prime.ℓ)
    (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D)
    (hCompat : QNormTateCompatibility T.scene1.data.link)
    (w : (IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate hCompat).badFinset) :
    (IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate hCompat).qOrder p w.1 =
      D.prime.qOrder w.1 (by
        have hwSource := IutQPilotSource.badFinset_mem_badPlacesOver p
          (IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate hCompat) w
        have hwLink : w.1 ∈ T.scene1.data.link.places := by
          exact (IutQPilotSource.mem_badPlacesOver_iff_link p
            (IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate hCompat) w.1).mp
            hwSource
        rw [hCompat.places_eq] at hwLink
        rw [hTate] at hwLink
        exact (Set.ext_iff.mp (iutInitialThetaTateParameterData_places_eq D) w.1).mpr hwLink) := by
  let S := IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate hCompat
  have hwSource : w.1 ∈ S.badPlacesOver := S.badFinset_mem_badPlacesOver p w
  have hwLink : w.1 ∈ T.scene1.data.link.places :=
    (S.mem_badPlacesOver_iff_link p w.1).mp hwSource
  have hwBad : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
    rw [hCompat.places_eq] at hwLink
    rw [hTate] at hwLink
    exact (Set.ext_iff.mp (iutInitialThetaTateParameterData_places_eq D) w.1).mpr hwLink
  calc
    S.qOrder p w.1 = T.scene1.data.link.tate.qOrder w.1 := S.qOrder_eq_link p hwSource
    _ = Arithmetic.completionQOrder w.1 (T.scene1.data.link.tate.parameter w.1) := rfl
    _ = Arithmetic.completionQOrder w.1 (D.prime.tate w.1 hwBad).q := by
      rw [hTate]
      have hwCanonical : w.1 ∈
          (AdelicThetaLinkData.ofInitialThetaData D
            T.scene1.data.link.theta
            T.scene1.data.link.thetaBase
            T.scene1.data.link.packetHull
            T.scene1.data.link.heightData
            T.scene1.data.link.ramification
            T.scene1.data.link.logVolume
            T.scene1.data.link.processionLength).places := by
        exact (Set.ext_iff.mp
          (iutInitialThetaLink_places_eq_badPlacesOver D
            T.scene1.data.link.theta
            T.scene1.data.link.thetaBase
            T.scene1.data.link.packetHull
            T.scene1.data.link.heightData
            T.scene1.data.link.ramification
            T.scene1.data.link.logVolume
            T.scene1.data.link.processionLength) w.1).mp hwBad
      have hParam := iutInitialThetaLink_parameter_eq_prime_tate D
        T.scene1.data.link.theta
        T.scene1.data.link.thetaBase
        T.scene1.data.link.packetHull
        T.scene1.data.link.heightData
        T.scene1.data.link.ramification
        T.scene1.data.link.logVolume
        T.scene1.data.link.processionLength hwCanonical hwBad
      exact congrArg (Arithmetic.completionQOrder w.1)
        (by simpa [AdelicThetaLinkData.ofInitialThetaData,
          AdelicThetaLinkData.ofTateParameters] using hParam)
    _ = D.prime.qOrder w.1 hwBad :=
      IutCompletionTateValuation.completion_qOrder_eq_initialTheta_qOrder D w.1 hwBad

end
end JoshiTeich.Act1Scene1
