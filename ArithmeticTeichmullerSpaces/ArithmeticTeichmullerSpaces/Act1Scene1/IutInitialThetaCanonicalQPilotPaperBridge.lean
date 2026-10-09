import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalQPilot
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQNormalizationBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-CANONICAL-QPILOT-PAPER-BRIDGE
source: the actual `InitialThetaData.prime` and its canonical
`AdelicThetaLinkData.ofInitialThetaData`; local paper normalization is from
`PaperQNormalizationBridge` and the q-pilot source contract is from
`IutInitialThetaCanonicalQPilot`.
fidelity: specializes the weighted paper-normalized q-sum identity to the
canonical q-pilot source supplied by real `InitialThetaData`. The result keeps
the q-pilot arithmetic weight and does not identify the source carrier with
the paper's unweighted `(p,w)` representatives.
boundary: Scene1/Derived
-/

/-! The canonical source carries the paper-normalized weighted q-sum once its
finite-place carrier is the canonical link assembled from the same datum. -/
theorem IutQPilotSource.absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum_ofCanonicalInitialThetaLink
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
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
      exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase
        packetHull heightData ramification logVolume processionLength
    let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
      packetHull heightData ramification logVolume processionLength hEll hLink
    let Q := S.toSceneQPilot p hCompat
    Q.absLogQ p =
      ∑ w : Q.badFinset,
        Arithmetic.qPilotWeight w.1 *
          -Real.log
            (Corollary312PaperNormalizedSourceQFactor p T
              (show Corollary312SourceQIndex p T from
                ⟨w.1, Q.mem_bad p w.2⟩)) := by
  let hCompat : QNormTateCompatibility T.scene1.data.link := by
    rw [hLink]
    exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase
      packetHull heightData ramification logVolume processionLength
  let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
    packetHull heightData ramification logVolume processionLength hEll hLink
  let Q := S.toSceneQPilot p hCompat
  have hNorm := S.toSceneQPilot_rawQNormDegreeNormalization p hCompat
  have hEllPos : 0 < T.ell := by
    rw [hEll]
    have h : 5 ≤ D.prime.ℓ := D.prime.five_le
    omega
  simpa [hCompat, S, Q] using
    (absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum
      p T Q S.orderCompatibility hNorm hEllPos)

end

end JoshiTeich.Act1Scene1
