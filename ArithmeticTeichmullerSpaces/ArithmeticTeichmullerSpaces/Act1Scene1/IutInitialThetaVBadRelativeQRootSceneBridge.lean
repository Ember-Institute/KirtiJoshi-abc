import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRelativeQRootProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQPilotReferenceBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-RELATIVE-QROOT-SCENE-BRIDGE
source: actual reference q-pilot identity and the canonical Scene1/reference bridge.
fidelity: identifies the canonical Scene1 q-pilot with the normalized relative
root product on exactly actual VBad. No source coverage, free sum equality or
theta-volume estimate is supplied by the caller.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

theorem Corollary312QPilotData.absLogQ_eq_normalizedVBadRelativeQRootProduct_negLog_ofCanonicalInitialThetaLink
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (hEll : T.ell = D.prime.ℓ)
    (hLink : T.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength) :
    let hCompat : QNormTateCompatibility T.scene1.data.link := by
      rw [hLink]
      exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase packetHull
        heightData ramification logVolume processionLength
    let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
      packetHull heightData ramification logVolume processionLength hEll hLink
    (S.toSceneQPilot p hCompat).absLogQ p =
      -Real.log (iutInitialThetaNormalizedVBadRelativeQRootProduct D) := by
  have heq :=
    Corollary312QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
      p D theta thetaBase packetHull heightData ramification logVolume processionLength hEll hLink
  exact heq.trans (iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D).symm

end
end JoshiTeich.Act1Scene1
