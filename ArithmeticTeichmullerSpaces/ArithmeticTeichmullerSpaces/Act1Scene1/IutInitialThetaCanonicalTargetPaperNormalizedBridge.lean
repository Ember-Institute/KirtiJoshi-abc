import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalQPilotPaperBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTateQPilotTargetAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalRawTargetAccounting

/-!
source-id: JT-SCENE1-CANONICAL-TARGET-PAPER-NORMALIZED-BRIDGE
source: canonical Tate q-family target accounting and the paper-normalized
q-factor bridge; Joshi III 3617--3650.
fidelity: identifies the raw target qLogSum with the global degree times
the weighted paper-normalized source factor sum, on the same canonical
InitialThetaData carrier. The legacy degree-one bundle gives the unscaled sum.
The finite source carrier, q-pilot weights and paper normalization remain
explicit; no unweighted paper representative sum or theta-volume identity is
introduced.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open NumberField
universe u
noncomputable section

theorem canonicalTateTarget_qLogSum_eq_weightedPaperNormalizedSourceQFactorLogSum
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
    (hDegree : Module.finrank ℚ D.F = 1) :
    Corollary312Data.qLogSum p base.target =
      let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
        p D base hEll hLink hDegree
      ∑ w : (C.qPilot p).badFinset,
        Arithmetic.qPilotWeight w.1 *
          -Real.log (Corollary312PaperNormalizedSourceQFactor p base.target
            (show Corollary312SourceQIndex p base.target from
              ⟨w.1, (C.qPilot p).mem_bad p w.2⟩)) := by
  let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink hDegree
  have hq := Corollary312Scene1QPilotData.qLogSum_eq_absLogQ p C
  have hp := absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum
    p C.base.target (C.qPilot p) C.source.orderCompatibility
    (C.rawNormalization p) C.base.ell_prime.pos
  exact hq.trans hp

/-- Raw target accounting retains the global degree on the same source carrier. -/
theorem canonicalTateQFamily_qLogSum_eq_degree_mul_weightedPaperNormalizedSourceQFactorLogSum
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p} {V : Corollary312VolumeData p T}
    (Q : Corollary312TateQFamily p T V)
    (hEll : T.ell = D.prime.ℓ)
    (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D) :
    let S := IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate Q.compatibility
    let P := S.toSceneQPilot p Q.compatibility
    Corollary312Data.qLogSum p T = (Module.finrank ℚ D.F : ℝ) *
      ∑ w : P.badFinset,
        Arithmetic.qPilotWeight w.1 *
          -Real.log (Corollary312PaperNormalizedSourceQFactor p T
            (show Corollary312SourceQIndex p T from ⟨w.1, P.mem_bad p w.2⟩)) := by
  let S := IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate Q.compatibility
  let P := S.toSceneQPilot p Q.compatibility
  have hraw := canonicalTateQFamily_qLogSum_eq_degree_mul_reference p D Q hEll hTate
  have href := canonicalTateSource_absLogQ_eq_reference p D hEll hTate Q.compatibility
  have hell : 0 < T.ell := by rw [hEll]; exact D.prime.ℓ_prime.pos
  have hpaper := absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum
    p T P S.orderCompatibility (S.toSceneQPilot_rawQNormDegreeNormalization p Q.compatibility) hell
  exact hraw.trans (congrArg ((Module.finrank ℚ D.F : ℝ) * ·) (href.symm.trans hpaper))

theorem canonicalTateQFamily_degreeNormalized_qLogSum_eq_weightedPaperNormalizedSourceQFactorLogSum
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p} {V : Corollary312VolumeData p T}
    (Q : Corollary312TateQFamily p T V)
    (hEll : T.ell = D.prime.ℓ)
    (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D) :
    let S := IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate Q.compatibility
    let P := S.toSceneQPilot p Q.compatibility
    Corollary312Data.qLogSum p T / (Module.finrank ℚ D.F : ℝ) =
      ∑ w : P.badFinset,
        Arithmetic.qPilotWeight w.1 *
          -Real.log (Corollary312PaperNormalizedSourceQFactor p T
            (show Corollary312SourceQIndex p T from ⟨w.1, P.mem_bad p w.2⟩)) := by
  let S := IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate Q.compatibility
  let P := S.toSceneQPilot p Q.compatibility
  have hRaw := canonicalTateQFamily_qLogSum_eq_degree_mul_weightedPaperNormalizedSourceQFactorLogSum
    p D Q hEll hTate
  have hDegree : (Module.finrank ℚ D.F : ℝ) ≠ 0 :=
    ne_of_gt Arithmetic.finrank_pos
  rw [hRaw]
  field_simp

end
end JoshiTeich.Act1Scene1
