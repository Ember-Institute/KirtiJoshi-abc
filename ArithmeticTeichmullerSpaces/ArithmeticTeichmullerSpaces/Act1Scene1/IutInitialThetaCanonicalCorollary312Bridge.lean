import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalVBadQProductBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-COR312-BRIDGE
source: the canonical q-pilot exponential qProduct bound and the existing
normalized q-family Corollary 3.12 consumer.
fidelity: assembles Corollary 3.12 under explicit actual-hull, q-family,
q-sum, and side-condition hypotheses. It does not construct those
hypotheses from the paper theta or Bloch--Kato model.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem corollary312_of_canonicalInitialThetaLink_of_actualHullVolume
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hLink : base.target.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D
        base.target.scene1.data.link.theta
        base.target.scene1.data.link.thetaBase
        base.target.scene1.data.link.packetHull
        base.target.scene1.data.link.heightData
        base.target.scene1.data.link.ramification
        base.target.scene1.data.link.logVolume
        base.target.scene1.data.link.processionLength)
    (hDegree : Module.finrank ℚ D.F = 1)
    (n : ℕ) (hn : 0 < n)
    (σ : iutInitialThetaVBadModuliFinset D → Fin n →
      (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
    (V : Corollary312VolumeData p base.target)
    (Q : Corollary312QFamily p base.target V)
    (N : Corollary312VolumeNormalization p base.target)
    (hlength : base.target.ellStar = n)
    (hq : Corollary312Data.qLogSum p base.target =
      iutInitialThetaSelectedQRootPaperSum D)
    (hvolume : base.target.thetaVolume =
      VBadThetaCollatedHull.volume D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ))
    (hEllPrime : Nat.Prime base.target.ell)
    (hEllGeFive : 5 ≤ base.target.ell)
    (hEllStarEq : base.target.ellStar = (base.target.ell - 1) / 2)
    (hEllStarPos : 0 < base.target.ellStar) :
    Corollary312 p base.target := by
  have hLower := canonicalScene1Exp_neg_procession_mul_absLogQ_ge_qProduct_of_actualHullVolume
    p D base hEll hLink hDegree n hn σ hσ V Q N hlength hq hvolume
  have hTheta := canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_absLogQ_of_actualHullVolume
    p D base hEll hLink hDegree n hn σ hσ N hvolume
  have hLower' : base.target.thetaVolume ≥
      Corollary312Data.qProduct p base.target V.qFactor := by
    rw [hTheta]
    exact hLower
  exact corollary312_of_q_family_normalized_lower_bound p base.target V Q N
    hEllPrime hEllGeFive hEllStarEq hEllStarPos hLower'

end
end JoshiTeich.Act1Scene1
