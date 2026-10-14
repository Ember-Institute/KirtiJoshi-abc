import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTateQPilotReferenceBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotTransferBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-TATE-QPILOT-TARGET-ACCOUNTING
source: Tate q-family source-sum identity, source-index q-pilot bridge, and
the Tate-only reference absLogQ bridge.
fidelity: connects target `qLogSum` to the actual reference q-pilot under the
explicit Tate-only Scene1 bundle. The paper representative carrier and any
unweighted paper accounting remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem Corollary312Scene1QPilotData.qLogSum_eq_absLogQ
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (B : Corollary312Scene1QPilotData (K := K) (O := O) p) :
    Corollary312Data.qLogSum p B.base.target = (B.qPilot p).absLogQ p := by
  have hSource := Corollary312TateQFamily.qLogSum_eq_sourceQLogSum
    p B.base.qFamily
  have hPilot := Corollary312QPilotSourceIndexBridge.absLogQ_eq_sourceQLogSum
    p B.source.orderCompatibility B.sourceNormalization B.base.ell_prime.pos
    (B.sourceIndexBridge p)
  exact hSource.trans hPilot.symm

theorem Corollary312Scene1QPilotData.qLogSum_eq_reference_ofCanonicalInitialThetaTateData
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
    Corollary312Data.qLogSum p base.target =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  let B := Corollary312Scene1QPilotData.ofCanonicalInitialThetaTateData
    p D base hEll hTate hDegree
  calc
    Corollary312Data.qLogSum p base.target = (B.qPilot p).absLogQ p :=
      Corollary312Scene1QPilotData.qLogSum_eq_absLogQ p B
    _ = JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
      exact Corollary312Scene1QPilotData.absLogQ_eq_reference_ofCanonicalInitialThetaTateData
        p D base hEll hTate hDegree

end
end JoshiTeich.Act1Scene1
