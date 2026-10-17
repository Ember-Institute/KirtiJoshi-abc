import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTateQPilotData
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotRawDegreeAccounting

/-!
source-id: JT-SCENE1-CANONICAL-TATE-RAW-ACCOUNTING-WITHOUT-BASE
source: actual Tate source, local q-order alignment and raw degree accounting.
fidelity: derives target qLogSum from Tate q-family data without accepting
Scene1 accounting, a volume estimate, or a degree-one normalization. The raw
degree coefficient is retained; paper representatives remain a separate issue.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable {T : Corollary312Data D.F O p}

theorem canonicalTateSource_absLogQ_eq_reference
    (hEll : T.ell = D.prime.ℓ)
    (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    ((IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate hCompat).toSceneQPilot
      p hCompat).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
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
        _ = (↑T.scene1.data.link.places :
            Set (NumberField.FinitePlace D.F)) := S.badPlacesOver_eq_link
        _ = (↑T.scene1.data.link.tate.places :
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
      Q.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) =
        R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ) := by
    intro w
    have hwSource : w.1 ∈ S.badPlacesOver := by
      exact S.badFinset_spec ▸ Finset.mem_coe.mpr w.2
    have hq := IutQPilotSource.qOrder_eq_initialTheta_qOrder_ofCanonicalTateData
      p D hEll hTate hCompat w
    have hqLink : S.qOrder p w.1 =
        T.scene1.data.link.tate.qOrder w.1 :=
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
    Q.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
        Real.log (Arithmetic.residueChar w.1) =
      (R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ)) *
        Real.log (Arithmetic.residueChar w.1) := by
          rw [← htw]
    _ = R.weight w.1 * (D.prime.qOrder w.1 (R.mem_bad w.2) : ℝ) *
        Real.log (JoshiTeich.ReferenceIut.residueChar w.1) := by rfl


theorem canonicalTateQFamily_qLogSum_eq_degree_mul_reference
    {V : Corollary312VolumeData p T}
    (Q : Corollary312TateQFamily p T V)
    (hEll : T.ell = D.prime.ℓ)
    (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D) :
    Corollary312Data.qLogSum p T = (Module.finrank ℚ D.F : ℝ) *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  let S := IutQPilotSource.ofInitialThetaCanonicalTateData D p hEll hTate Q.compatibility
  let P := S.toSceneQPilot p Q.compatibility
  have hRaw := S.toSceneQPilot_rawQNormDegreeNormalization p Q.compatibility
  have hEllPos : 0 < T.ell := by
    rw [hEll]
    exact lt_of_lt_of_le (by decide : 0 < 5) D.prime.five_le
  rw [Corollary312RawTargetSpecification.qLogSum_eq_rawSourceQLogSum p
    (Corollary312RawTargetSpecification.ofTateQFamily p Q)]
  have hSum := Corollary312QPilotSourceIndexBridge.rawSourceQLogSum_eq_degree_mul_absLogQ
    p S.orderCompatibility hRaw hEllPos
    (Corollary312QPilotSourceIndexBridge.ofGrouping p T V P Q)
  exact hSum.trans (congrArg ((Module.finrank ℚ D.F : ℝ) * ·)
    (canonicalTateSource_absLogQ_eq_reference p D hEll hTate Q.compatibility))

theorem canonicalTateScene1Data_qLogSum_eq_degree_mul_reference
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hTate : base.target.scene1.data.link.tate =
      iutInitialThetaTateParameterData D) :
    Corollary312Data.qLogSum p base.target =
      (Module.finrank ℚ D.F : ℝ) *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  exact canonicalTateQFamily_qLogSum_eq_degree_mul_reference p D
    base.qFamily hEll hTate

end
end JoshiTeich.Act1Scene1
