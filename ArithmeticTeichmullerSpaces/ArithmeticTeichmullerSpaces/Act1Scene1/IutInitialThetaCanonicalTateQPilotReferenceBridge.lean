import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTateQPilotData

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-TATE-QPILOT-REFERENCE
source: Tate-only canonical q-pilot source, actual finite-place carrier, and
reference InitialThetaData q-pilot accounting.
fidelity: transports the q-pilot absLogQ equality to the reference datum using
only the Tate-family equality and the proved local q-order alignment. It does
not identify the carrier with paper representatives or assert theta/BK volume
identities.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem Corollary312Scene1QPilotData.absLogQ_eq_reference_ofCanonicalInitialThetaTateData
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
    let B := Corollary312Scene1QPilotData.ofCanonicalInitialThetaTateData
      p D base hEll hTate hDegree
    (B.qPilot p).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  let hCompat : QNormTateCompatibility base.target.scene1.data.link :=
    base.qFamily.compatibility
  let S := IutQPilotSource.ofInitialThetaCanonicalTateData
    D p hEll hTate hCompat
  let Q := S.toSceneQPilot p hCompat
  let R := IutTorsionQRootSource.iutInitialThetaQPilotData D
  have hFin : Q.badFinset = R.badFinset := by
    have hSet : (↑Q.badFinset : Set (NumberField.FinitePlace D.F)) =
        (↑R.badFinset : Set (NumberField.FinitePlace D.F)) := by
      calc
        (↑Q.badFinset : Set (NumberField.FinitePlace D.F)) = S.badPlacesOver :=
          S.badFinset_spec
        _ = (↑base.target.scene1.data.link.places :
            Set (NumberField.FinitePlace D.F)) := S.badPlacesOver_eq_link
        _ = (↑base.target.scene1.data.link.tate.places :
            Set (NumberField.FinitePlace D.F)) := by
          rw [hCompat.places_eq]
        _ = (↑(iutInitialThetaTateParameterData D).places :
            Set (NumberField.FinitePlace D.F)) := by rw [hTate]
        _ = JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
          (iutInitialThetaTateParameterData_places_eq D).symm
        _ = (↑R.badFinset : Set (NumberField.FinitePlace D.F)) :=
          R.badFinset_spec.symm
    apply Finset.ext
    intro w
    exact Set.ext_iff.mp hSet w
  have hTerm : ∀ w : Q.badFinset,
      Q.weight w.1 * (base.target.scene1.data.link.tate.qOrder w.1 : ℝ) =
        R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ) := by
    intro w
    have hwSource : w.1 ∈ S.badPlacesOver := by
      exact S.badFinset_spec ▸ Finset.mem_coe.mpr w.2
    have hq := IutQPilotSource.qOrder_eq_initialTheta_qOrder_ofCanonicalTateData
      p D hEll hTate hCompat w
    have hqLink : S.qOrder p w.1 =
        base.target.scene1.data.link.tate.qOrder w.1 :=
      S.qOrder_eq_link p hwSource
    have hWeight : Q.weight w.1 = R.weight w.1 := rfl
    rw [hWeight, ← hqLink, ← hq]
  change Q.absLogQ p = JoshiTeich.ReferenceIut.QPilotData.absLogQ R
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
    Q.weight w.1 * (base.target.scene1.data.link.tate.qOrder w.1 : ℝ) *
        Real.log (Arithmetic.residueChar w.1) =
      (R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ)) *
        Real.log (Arithmetic.residueChar w.1) := by
          rw [← htw]
    _ = R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ) *
        Real.log (JoshiTeich.ReferenceIut.residueChar w.1) := by rfl

end
end JoshiTeich.Act1Scene1
