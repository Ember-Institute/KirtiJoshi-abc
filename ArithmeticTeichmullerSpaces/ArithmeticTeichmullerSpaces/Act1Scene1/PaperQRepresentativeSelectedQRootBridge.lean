import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootPaperQSum
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperRootNormProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.AdelicThetaLinkBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open scoped BigOperators

universe u

noncomputable section

/-!
source-id: IUT-COR312-PAPER-REPRESENTATIVE-SELECTED-QROOT-BRIDGE
source: the actual `InitialThetaData` section and canonical section link, together
with `cor:cor312` and the finite q-pilot representative accounting certificate.
fidelity: makes the finite equivalence from paper representatives to the
canonical section-link places and the representative local-term certificate
explicit; the certificate is still a Scene1 source obligation.
boundary: Scene1/Derived

This module does not claim that the paper's `L'` representative choice has
already been constructed.  It records exactly the finite data needed to
transport its unweighted q-sum to the selected q-root carrier.
-/

structure Corollary312PaperRepresentativeSectionLinkAccounting
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    {P : Corollary312QPilotData p T}
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    (theta : ThetaPilotData ↥D.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) where
  /-- The paper representative carrier is identified with the canonical link places. -/
  representativeLinkEquiv :
    A.representative ≃
      {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ (AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
          packetHull heightData ramification logVolume processionLength).places}
  /-- The representative term is the canonical paper-normalized q-order term. -/
  representativeTerm_eq : ∀ r : A.representative,
    A.representativeTerm r =
      (((AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
          packetHull heightData ramification logVolume processionLength).tate.qOrder
          (representativeLinkEquiv r).1 : ℝ) /
        (2 * (D.prime.ℓ : ℝ))) *
        Real.log (Arithmetic.residueChar (representativeLinkEquiv r).1)

namespace Corollary312PaperRepresentativeSectionLinkAccounting

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

noncomputable def selectedQRootPaperNormalizedFactorProduct
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : ℝ := by
  classical
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let _ : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  exact ∏ s : S, Real.exp (-(
    (Arithmetic.ramIdx s.1.1 : ℝ) *
      Arithmetic.ordp s.1.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1) *
      Real.log (Arithmetic.residueChar s.1.1)))

theorem representativeSum_eq_sectionLinkQLogSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    {P : Corollary312QPilotData p T}
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D p A theta thetaBase
      packetHull heightData ramification logVolume processionLength) :
    let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
      packetHull heightData ramification logVolume processionLength
    let W := {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ L.places}
    letI : Fintype W := Fintype.ofFinset L.places (fun _ => Iff.rfl)
    (∑ r : A.representative, A.representativeTerm r) =
      ∑ w : W,
        (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
          Real.log (Arithmetic.residueChar w.1)) := by
  classical
  let _ := A.representativeDecidableEq
  let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
    packetHull heightData ramification logVolume processionLength
  let W := {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ L.places}
  let _ : Fintype W := Fintype.ofFinset L.places (fun _ => Iff.rfl)
  let e := B.representativeLinkEquiv
  calc
    (∑ r : A.representative, A.representativeTerm r) =
        ∑ r : A.representative,
          (((L.tate.qOrder (e r).1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
            Real.log (Arithmetic.residueChar (e r).1)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact B.representativeTerm_eq r
    _ = ∑ w : W,
        (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
          Real.log (Arithmetic.residueChar w.1)) := by
      simpa using e.sum_comp (fun w =>
        (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
          Real.log (Arithmetic.residueChar w.1)))

theorem representativeSum_eq_selectedQRootPaperQLogSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    {P : Corollary312QPilotData p T}
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D p A theta thetaBase
      packetHull heightData ramification logVolume processionLength) :
    let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    (∑ r : A.representative, A.representativeTerm r) =
      ∑ s : S,
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1) := by
  classical
  let _ := A.representativeDecidableEq
  let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
    packetHull heightData ramification logVolume processionLength
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let _ : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  have hSection :=
    iutInitialThetaOddSupportSelectedQRootSourcePlaces_paperQLogSum_eq_sectionLink_unGrouped
      D theta thetaBase packetHull heightData ramification logVolume processionLength
  calc
    (∑ r : A.representative, A.representativeTerm r) =
        ∑ w : {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ L.places},
          (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
            Real.log (Arithmetic.residueChar w.1)) :=
      representativeSum_eq_sectionLinkQLogSum p D A theta thetaBase packetHull
        heightData ramification logVolume processionLength B
    _ = ∑ s : S,
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1) := by
      exact hSection.symm

theorem representativePaperNormalizedSourceQFactorProduct_eq_selectedQRootPaperNormalizedFactorProduct
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    {P : Corollary312QPilotData p T}
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D p A theta thetaBase
      packetHull heightData ramification logVolume processionLength) :
    Corollary312QPilotPaperRepresentativeAccounting.representativePaperNormalizedSourceQFactorProduct
        p A = selectedQRootPaperNormalizedFactorProduct D := by
  classical
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let _ : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  have hsum := representativeSum_eq_selectedQRootPaperQLogSum p D A theta thetaBase
    packetHull heightData ramification logVolume processionLength B
  unfold Corollary312QPilotPaperRepresentativeAccounting.representativePaperNormalizedSourceQFactorProduct
  calc
    (∏ r : A.representative, Real.exp (-A.representativeTerm r)) =
        Real.exp (-(∑ r : A.representative, A.representativeTerm r)) := by
      rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    _ = Real.exp (-∑ s : S,
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1)) := by
      rw [hsum]
    _ = selectedQRootPaperNormalizedFactorProduct D := by
      unfold selectedQRootPaperNormalizedFactorProduct
      rw [← Real.exp_sum, ← Finset.sum_neg_distrib]

theorem selectedQRootPaperNormalizedFactorProduct_eq_actualSelectedPaperRootNormProduct
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    selectedQRootPaperNormalizedFactorProduct D = actualSelectedPaperRootNormProduct D := by
  classical
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let _ : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  unfold selectedQRootPaperNormalizedFactorProduct actualSelectedPaperRootNormProduct
  apply Finset.prod_congr rfl
  intro s hs
  have hpos : 0 < actualPaperRootNorm D s.1 :=
    (actualPaperRootNorm_mem_Ioo_via_rootBallHaar D s.1).1
  calc
    Real.exp (-((Arithmetic.ramIdx s.1.1 : ℝ) *
        Arithmetic.ordp s.1.1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1) *
        Real.log (Arithmetic.residueChar s.1.1))) =
      Real.exp (Real.log (actualPaperRootNorm D s.1)) := by
        congr 1
        linarith [actualPaperRootNorm_negLog_eq_paperTerm D s.1]
    _ = actualPaperRootNorm D s.1 := Real.exp_log hpos

theorem representativePaperNormalizedSourceQFactorProduct_eq_actualSelectedPaperRootNormProduct
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    {P : Corollary312QPilotData p T}
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D p A theta thetaBase
      packetHull heightData ramification logVolume processionLength) :
    Corollary312QPilotPaperRepresentativeAccounting.representativePaperNormalizedSourceQFactorProduct
        p A = actualSelectedPaperRootNormProduct D := by
  rw [representativePaperNormalizedSourceQFactorProduct_eq_selectedQRootPaperNormalizedFactorProduct
      p D A theta thetaBase packetHull heightData ramification logVolume processionLength B,
    selectedQRootPaperNormalizedFactorProduct_eq_actualSelectedPaperRootNormProduct D]

/-- Once the two finite source certificates are supplied, the weighted q-pilot
sum transports directly to the unweighted selected q-root paper sum. -/
theorem absLogQ_eq_selectedQRootPaperQLogSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    {P : Corollary312QPilotData p T}
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D p A theta thetaBase
      packetHull heightData ramification logVolume processionLength)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    P.absLogQ p =
      ∑ s : S,
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1) := by
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let _ : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  have hWeighted :=
    Corollary312QPilotPaperRepresentativeAccounting.absLogQ_eq_unweightedRepresentativeSum
      p A hOrder hNorm hEll
  calc
    P.absLogQ p = ∑ r : A.representative, A.representativeTerm r := hWeighted
    _ = ∑ s : S,
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1) :=
      representativeSum_eq_selectedQRootPaperQLogSum p D A theta thetaBase packetHull
        heightData ramification logVolume processionLength B

end Corollary312PaperRepresentativeSectionLinkAccounting

/-! The Scene1 q-pilot bundle exposes the same raw normalization contract as
the source adapter.  This wrapper consumes that projection together with the
explicit representative and section-link certificates. -/
theorem Corollary312Scene1QPilotData.absLogQ_eq_selectedQRootPaperQLogSum
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D₀ : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (D : Corollary312Scene1QPilotData (K := D₀.F) (O := O) p)
    (A : Corollary312QPilotPaperRepresentativeAccounting p D.base.target
      (D.qPilot p))
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D₀.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D₀.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D₀.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D₀ p A theta
      thetaBase packetHull heightData ramification logVolume processionLength) :
    let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D₀).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D₀}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D₀).fintype
    (D.qPilot p).absLogQ p =
      ∑ s : S,
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D₀).qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1) := by
  exact Corollary312PaperRepresentativeSectionLinkAccounting.absLogQ_eq_selectedQRootPaperQLogSum
    p D₀ A theta thetaBase packetHull heightData ramification logVolume processionLength B
    D.source.orderCompatibility (D.rawNormalization p) D.base.ell_prime.pos

end

end JoshiTeich.Act1Scene1
