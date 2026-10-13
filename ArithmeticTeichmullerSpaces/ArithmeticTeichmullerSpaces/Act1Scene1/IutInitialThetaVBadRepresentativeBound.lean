import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullRepresentativeBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQPilotReferenceBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-REPRESENTATIVE-BOUND
source: actual VBad inclusion, the equality of full-support and admissible-prime
Tate orders on their common carrier, full representative accounting, and the
canonical Scene1/reference q-pilot bridge.
fidelity: identifies the actual VBad q-pilot with the restriction of the full
odd-support sum, then bounds the actual and canonical Scene1 q-pilots by the
selected paper sum. No full/VBad equality or theta-volume estimate is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

theorem iutInitialThetaReferenceAbsLogQ_eq_fullCarrierRestriction
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) =
      ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        if b.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
          iutInitialThetaBaseQPilotLogTerm D b else 0 := by
  let Q := IutTorsionQRootSource.iutInitialThetaQPilotData D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let f : Q.badFinset → B.badFinset := fun w => ⟨w.1, by
    apply (Set.ext_iff.mp B.badFinset_spec w.1).mpr
    exact iutBadPlacesOver_subset_oddMultiplicativeSupport D (Q.mem_bad w.2)⟩
  have hlocal (w : Q.badFinset) :
      Q.weight w.1 * (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
          Real.log (JoshiTeich.ReferenceIut.residueChar w.1) /
            (2 * (D.prime.ℓ : ℝ)) = iutInitialThetaBaseQPilotLogTerm D (f w) := by
    unfold iutInitialThetaBaseQPilotLogTerm
    rw [iutInitialThetaOddSupportBaseQPilotSource_qOrder_eq_admissiblePrime D (f w)
      (Q.mem_bad w.2)]
    change Arithmetic.qPilotWeight w.1 * (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
      Real.log (Arithmetic.residueChar w.1) / (2 * (D.prime.ℓ : ℝ)) = _
    ring
  have hsum : Q.absLogQ = ∑ w : Q.badFinset, iutInitialThetaBaseQPilotLogTerm D (f w) := by
    change (∑ w : Q.badFinset,
      Q.weight w.1 * (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
        Real.log (JoshiTeich.ReferenceIut.residueChar w.1)) / (2 * (D.prime.ℓ : ℝ)) = _
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun w _ => hlocal w
  rw [hsum, ← Finset.sum_filter]
  refine Finset.sum_bij (fun w _ => f w) ?_ ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Q.mem_bad w.2⟩
  · intro w hw v hv h
    exact Subtype.ext (congrArg (fun b : B.badFinset => b.1) h)
  · intro b hb
    have hbQ : b.1 ∈ Q.badFinset :=
      (Set.ext_iff.mp Q.badFinset_spec b.1).mpr (Finset.mem_filter.mp hb).2
    exact ⟨⟨b.1, hbQ⟩, Finset.mem_univ _, Subtype.ext rfl⟩
  · intro w hw
    rfl

theorem iutInitialThetaReferenceAbsLogQ_le_fullBaseSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤
      iutInitialThetaFullBaseQPilotLogSum D := by
  rw [iutInitialThetaReferenceAbsLogQ_eq_fullCarrierRestriction]
  unfold iutInitialThetaFullBaseQPilotLogSum
  apply Finset.sum_le_sum
  intro b hb
  split_ifs
  · exact le_rfl
  · exact (iutInitialThetaBaseQPilotLogTerm_pos D b).le

theorem iutInitialThetaReferenceAbsLogQ_le_selectedPaperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  (iutInitialThetaReferenceAbsLogQ_le_fullBaseSum D).trans
    (iutInitialThetaFullBaseQPilotLogSum_le_selectedPaperSum D)

theorem Corollary312QPilotData.absLogQ_le_selectedPaperSum_ofCanonicalInitialThetaLink
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
    (S.toSceneQPilot p hCompat).absLogQ p ≤ iutInitialThetaSelectedQRootPaperSum D := by
  have heq :=
    Corollary312QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
      p D theta thetaBase packetHull heightData ramification logVolume processionLength hEll hLink
  exact heq.trans_le (iutInitialThetaReferenceAbsLogQ_le_selectedPaperSum D)

end
end JoshiTeich.Act1Scene1
