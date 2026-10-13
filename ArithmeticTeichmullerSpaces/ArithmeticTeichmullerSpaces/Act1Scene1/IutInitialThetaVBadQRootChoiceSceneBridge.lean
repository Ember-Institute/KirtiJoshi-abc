import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadQRootChoice
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRelativeQRootSceneBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-QROOT-CHOICE-SCENE-BRIDGE
source: actual VBad selector product identity and the canonical Scene1 q-pilot bridge.
fidelity: lets the actual Scene1 q-pilot consume any actual over-place selector,
with no separate injectivity, multiplicity or numerical equality certificate.
This does not construct the paper theta hull or a complete Scene1 model.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

theorem Corollary312QPilotData.absLogQ_eq_choiceVBadRelativeQRootProduct_negLog_ofCanonicalInitialThetaLink
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
        heightData ramification logVolume processionLength)
    (ρ : iutInitialThetaVBadModuliFinset D → (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hρ : ∀ v, Ideal.LiesOver (ρ v).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal) :
    let hCompat : QNormTateCompatibility T.scene1.data.link := by
      rw [hLink]
      exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase packetHull
        heightData ramification logVolume processionLength
    let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
      packetHull heightData ramification logVolume processionLength hEll hLink
    (S.toSceneQPilot p hCompat).absLogQ p =
      -Real.log (iutInitialThetaNormalizedVBadRelativeQRootProductOf D ρ) := by
  rw [iutInitialThetaNormalizedVBadRelativeQRootProductOf_eq_canonical D ρ hρ]
  exact Corollary312QPilotData.absLogQ_eq_normalizedVBadRelativeQRootProduct_negLog_ofCanonicalInitialThetaLink
    p D theta thetaBase packetHull heightData ramification logVolume processionLength hEll hLink

end
end JoshiTeich.Act1Scene1
