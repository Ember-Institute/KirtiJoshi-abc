import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalQPilotPaperBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open scoped BigOperators NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-QPILOT-REFERENCE-BRIDGE
source: the actual `InitialThetaData.prime` and the reference project's
`Iut.QPilotData.absLogQ`; the canonical Scene1 source is assembled by
`IutInitialThetaCanonicalQPilotPaperBridge`.
fidelity: identifies the adapted Scene1 q-pilot log-volume with the reference
q-pilot log-volume by transporting the finite carrier, arithmetic weight, and
the actual admissible-prime q-order. It does not identify the carrier with the
paper `L'` representatives or prove theta-volume accounting.
boundary: Scene1/Derived
-/

private theorem canonical_source_badFinset_eq_reference_badFinset
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
    (IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
      packetHull heightData ramification logVolume processionLength hEll hLink).badFinset =
      (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset := by
  let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
    packetHull heightData ramification logVolume processionLength hEll hLink
  let R := IutTorsionQRootSource.iutInitialThetaQPilotData D
  have hSbad : S.badPlacesOver =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
    calc
      S.badPlacesOver = (↑T.scene1.data.link.places : Set (FinitePlace D.F)) :=
        S.badPlacesOver_eq_link
      _ = (↑(AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
          heightData ramification logVolume processionLength).places :
          Set (FinitePlace D.F)) := by rw [hLink]
      _ = JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
        iutInitialThetaLink_places_eq_badPlacesOver D theta thetaBase packetHull
          heightData ramification logVolume processionLength |>.symm
  apply Finset.ext
  intro w
  have hSets : (↑S.badFinset : Set (FinitePlace D.F)) =
      (↑R.badFinset : Set (FinitePlace D.F)) := by
    calc
      (↑S.badFinset : Set (FinitePlace D.F)) = S.badPlacesOver := S.badFinset_spec
      _ = JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := hSbad
      _ = (↑R.badFinset : Set (FinitePlace D.F)) := R.badFinset_spec.symm
  exact Set.ext_iff.mp hSets w

theorem Corollary312QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
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
      exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase packetHull
        heightData ramification logVolume processionLength
    let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
      packetHull heightData ramification logVolume processionLength hEll hLink
    (S.toSceneQPilot p hCompat).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  let hCompat : QNormTateCompatibility T.scene1.data.link := by
    rw [hLink]
    exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase packetHull
      heightData ramification logVolume processionLength
  let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
    packetHull heightData ramification logVolume processionLength hEll hLink
  let Q := S.toSceneQPilot p hCompat
  let R := IutTorsionQRootSource.iutInitialThetaQPilotData D
  have hFin : Q.badFinset = R.badFinset := by
    exact canonical_source_badFinset_eq_reference_badFinset p D theta thetaBase
      packetHull heightData ramification logVolume processionLength hEll hLink
  have hTerm : ∀ w : Q.badFinset,
      Q.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) =
        R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ) := by
    intro w
    have hwS : w.1 ∈ S.badPlacesOver := by
      exact S.badFinset_spec ▸ Finset.mem_coe.mpr w.2
    have hq := IutQPilotSource.qOrder_eq_initialTheta_qOrder_ofCanonicalInitialThetaLink
      p D theta thetaBase packetHull heightData ramification logVolume processionLength hEll hLink w
    have hqLink : S.qOrder p w.1 = T.scene1.data.link.tate.qOrder w.1 :=
      S.qOrder_eq_link p hwS
    have hWeight : Q.weight w.1 = R.weight w.1 := rfl
    rw [hWeight, ← hqLink, ← hq]
  change Q.absLogQ p =
    JoshiTeich.ReferenceIut.QPilotData.absLogQ R
  unfold Corollary312QPilotData.absLogQ Corollary312QPilotData.logQ
  unfold JoshiTeich.ReferenceIut.QPilotData.absLogQ
    JoshiTeich.ReferenceIut.QPilotData.logQ
  rw [hEll]
  rw [hFin]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  have hwQ : w.1 ∈ Q.badFinset := by
    rw [hFin]
    exact w.2
  let wQ : Q.badFinset := ⟨w.1, hwQ⟩
  have htw := hTerm wQ
  calc
    Q.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
        Real.log (Arithmetic.residueChar w.1) =
      (R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ)) *
        Real.log (Arithmetic.residueChar w.1) := by
          rw [← htw]
    _ = R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ) *
        Real.log (JoshiTeich.ReferenceIut.residueChar w.1) := by rfl

end

end JoshiTeich.Act1Scene1
