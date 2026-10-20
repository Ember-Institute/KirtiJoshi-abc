import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaActualHullCostTransfer
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaActualRawVolumeBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalScene1Input
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadLogGeneratedHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTargetPaperNormalizedBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotSourceIndexBridge

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-DATA
source: actual InitialThetaData Tate parameters and section representatives;
S1.406 Haar cost transfer, S1.358 raw degree accounting; Joshi III 1028--1055,
3495--3557, and 3617--3645.
fidelity: assembles the actual ordinary-log cost carrier, target volume, raw
q-terms, finite grouping and q-family from one InitialThetaData. Remaining
theta/period/perfectoid laws are explicit analytic inputs. No target, q-family,
transfer bound, volume identity, degree-one hypothesis or tuple certificate is
an input. The paper theta/BK/untilt and representative identities remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance actualHullPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

abbrev PositivePacket :=
  ActualHullCostTransfer.PositivePacket D (length D) (tuple D) (tuple_liesOver D) (collation D)

variable (theta : ThetaPilotData D.F)
variable (route : PositivePacket D → theta.index)
variable (thetaBase : theta.index) (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)

abbrev packetHull :=
  ActualHullCostTransfer.packetHull D (length D) (tuple D) (tuple_liesOver D)
    (collation D) theta route

abbrev link :=
  ActualHullCostTransfer.link D (length D) (tuple D) (tuple_liesOver D)
    (collation D) theta route thetaBase heightData ramification

/-- Only the analytic laws not supplied by the actual arithmetic/Haar producers. -/
structure AnalyticInput where
  placeData : PerfectoidPlaceData D.F O p
  bridge : PerfectoidBridgeData (link D theta route thetaBase heightData ramification)
    p placeData
  thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase
  periodMap : ∀ i, theta.period i = theta.liftedLog i
  normalization : letI := theta.indexFintype
    cost D = ∑ i, theta.period i
  perfectoidBridge : PerfectoidBridgeLaws
    (link D theta route thetaBase heightData ramification) p placeData bridge
  theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)

variable (X : AnalyticInput (O := O) p D theta route thetaBase heightData ramification)

def toCanonicalInput :
    CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase
      (packetHull D theta route) heightData ramification (cost D) (length D) where
  placeData := X.placeData
  bridge := X.bridge
  thetaScaling := X.thetaScaling
  periodMap := X.periodMap
  normalization := X.normalization
  packet_weight_positive := ActualHullCostTransfer.packetWeight_pos
    D (length D) (tuple D) (tuple_liesOver D) (collation D) theta route
  hull_weight_positive := ActualHullCostTransfer.hullWeight_pos
    D (length D) (tuple D) (tuple_liesOver D) (collation D) theta route
  perfectoidBridge := X.perfectoidBridge
  theta_log_shell := X.theta_log_shell
  packetCollationHull := ActualHullCostTransfer.packetCollationHull
    D (length D) (tuple D) (tuple_liesOver D) (collation D) theta route
    thetaBase heightData ramification
  volumeTransfer := ActualHullCostTransfer.volumeTransfer
    D (length D) (tuple D) (tuple_liesOver D) (collation D) theta route
    (VBadThetaLogCollation.generator_coverage D (length D) (tuple D) (tuple_liesOver D))
    (VBadThetaLogCollation.collation_subset_normalization
      D (length D) (tuple D) (tuple_liesOver D)) thetaBase heightData ramification

def scene1Input : Scene1Input D.F O p :=
  CanonicalInitialThetaScene1Input.toScene1Input p D theta thetaBase
    (packetHull D theta route) heightData ramification (cost D) (length D)
    (toCanonicalInput p D theta route thetaBase heightData ramification X)

/-- Both target sides are fixed by the actual source, before proving the bound. -/
def data : Corollary312Data D.F O p where
  scene1 := scene1Input p D theta route thetaBase heightData ramification X
  ell := D.prime.ℓ
  ellStar := length D
  qIndex := ↥(iutInitialThetaTateParameterData D).places
  qIndexFintype := inferInstance
  qLogTerm w := -Real.log ((iutInitialThetaTateParameterData D).norm w.1 ^
    (1 / (2 * (D.prime.ℓ : ℝ))))
  thetaVolume := hullVolume D

theorem data_link_eq :
    (data p D theta route thetaBase heightData ramification X).scene1.data.link =
      link D theta route thetaBase heightData ramification := rfl

theorem data_thetaVolume_eq :
    (data p D theta route thetaBase heightData ramification X).thetaVolume =
      hullVolume D := rfl

theorem qNormCompatibility :
    QNormTateCompatibility (data p D theta route thetaBase heightData ramification X).scene1.data.link :=
  iutInitialThetaLink_qNormTateCompatibility D theta thetaBase
    (packetHull D theta route) heightData ramification (cost D) (length D)

theorem hullVolume_eq_exp_neg_coefficientWeightedPaperSum :
    hullVolume D =
      Real.exp (-(length D : ℝ) *
        (∑ v : iutInitialThetaVBadModuliFinset D,
          iutInitialThetaRepresentativeCoefficient D
              (iutInitialThetaVBadModuliAt D v) *
            VBadSelectedPaper.paperTerm D v)) := by
  exact VBadThetaLogCollation.volume_eq_exp_neg_coefficientWeightedPaperSum
    D (length D) (tuple D) (tuple_liesOver D)

def source : IutQPilotSource p (data p D theta route thetaBase heightData ramification X) :=
  IutQPilotSource.ofInitialThetaCanonicalTateData D p rfl rfl
    (qNormCompatibility p D theta route thetaBase heightData ramification X)

def indexEquiv :
    (data p D theta route thetaBase heightData ramification X).qIndex ≃
      Corollary312SourceQIndex p (data p D theta route thetaBase heightData ramification X) :=
  Equiv.refl _

def volumeData : Corollary312VolumeData p
    (data p D theta route thetaBase heightData ramification X) where
  qFactor w := (iutInitialThetaTateParameterData D).norm w.1 ^
    (1 / (2 * (D.prime.ℓ : ℝ)))

def qFamily : Corollary312TateQFamily p
    (data p D theta route thetaBase heightData ramification X)
    (volumeData p D theta route thetaBase heightData ramification X) where
  compatibility := qNormCompatibility p D theta route thetaBase heightData ramification X
  grouping := Corollary312SourceQGrouping.ofIutSource p
    (data p D theta route thetaBase heightData ramification X)
    (source p D theta route thetaBase heightData ramification X)
    (qNormCompatibility p D theta route thetaBase heightData ramification X)
    (indexEquiv p D theta route thetaBase heightData ramification X)
  indexEquiv := indexEquiv p D theta route thetaBase heightData ramification X
  grouping_place_eq _ := rfl
  qFactor_eq _ := rfl
  qLogTerm_eq _ := rfl

theorem qLogSum_eq_degree_mul_reference :
    Corollary312Data.qLogSum p (data p D theta route thetaBase heightData ramification X) =
      (Module.finrank ℚ D.F : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) :=
  InitialThetaRawQ.logSum_eq_degree_mul_reference D

theorem degreeNormalized_qLogSum_eq_reference :
    Corollary312Data.qLogSum p (data p D theta route thetaBase heightData ramification X) /
        (Module.finrank ℚ D.F : ℝ) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hDegree : (Module.finrank ℚ D.F : ℝ) ≠ 0 :=
    ne_of_gt Arithmetic.finrank_pos
  rw [qLogSum_eq_degree_mul_reference p D theta route thetaBase heightData ramification X]
  field_simp

theorem degreeNormalized_qLogSum_eq_weightedPaperNormalizedSourceQLogSum :
    Corollary312Data.qLogSum p (data p D theta route thetaBase heightData ramification X) /
        (Module.finrank ℚ D.F : ℝ) =
      Corollary312WeightedPaperNormalizedSourceQLogSum p
        (data p D theta route thetaBase heightData ramification X)
        (qFamily p D theta route thetaBase heightData ramification X).grouping := by
  exact canonicalTateQFamily_degreeNormalized_qLogSum_eq_weightedPaperNormalizedSourceQLogSum
    p D (qFamily p D theta route thetaBase heightData ramification X) rfl rfl

set_option maxHeartbeats 1000000 in
theorem qProduct_le_hullVolume :
    Corollary312Data.qProduct p
        (data p D theta route thetaBase heightData ramification X)
        (volumeData p D theta route thetaBase heightData ramification X).qFactor ≤
      hullVolume D := by
  unfold Corollary312Data.qProduct
  change
    (∏ i : (iutInitialThetaTateParameterData D).places,
      ((iutInitialThetaTateParameterData D).norm i.1 ^
        (1 / (2 * (D.prime.ℓ : ℝ)))) ^ (length D)) ≤ hullVolume D
  have hProd :
      (∏ i : (iutInitialThetaTateParameterData D).places,
        ((iutInitialThetaTateParameterData D).norm i.1 ^
          (1 / (2 * (D.prime.ℓ : ℝ)))) ^ (length D)) =
        (∏ i : (iutInitialThetaTateParameterData D).places,
          (iutInitialThetaTateParameterData D).norm i.1 ^
            (1 / (2 * (D.prime.ℓ : ℝ)))) ^ (length D) := by
    simpa using
      (Finset.prod_pow (Finset.univ : Finset (iutInitialThetaTateParameterData D).places)
        (length D)
        (fun i : (iutInitialThetaTateParameterData D).places =>
          (iutInitialThetaTateParameterData D).norm i.1 ^
            (1 / (2 * (D.prime.ℓ : ℝ)))) )
  rw [hProd]
  change
    (∏ i : (IutBaseQPilotSource.ofInitialThetaData D).badFinset,
      (iutInitialThetaTateParameterData D).norm i.1 ^
        (1 / (2 * (D.prime.ℓ : ℝ)))) ^ (length D) ≤ hullVolume D
  simpa [Finset.prod_attach, InitialThetaRawQ.product, InitialThetaRawQ.factor,
    iutInitialThetaTateParameterData] using
    (InitialThetaRawQ.product_pow_le_actualVolume D (length D) (tuple D)
      (tuple_liesOver D))

theorem thetaVolume_ge_qProduct :
    (data p D theta route thetaBase heightData ramification X).thetaVolume ≥
      Corollary312Data.qProduct p
        (data p D theta route thetaBase heightData ramification X)
        (volumeData p D theta route thetaBase heightData ramification X).qFactor := by
  rw [data_thetaVolume_eq p D theta route thetaBase heightData ramification X]
  exact qProduct_le_hullVolume p D theta route thetaBase heightData ramification X

theorem volumeNormalization : Corollary312VolumeNormalization p
    (data p D theta route thetaBase heightData ramification X) :=
  actualCostLink_volumeNormalization p D (length D) (tuple D) (tuple_liesOver D)
    theta route thetaBase heightData ramification
    (data p D theta route thetaBase heightData ramification X) rfl rfl

theorem transferLogBound : Corollary312TransferLogBound p
    (data p D theta route thetaBase heightData ramification X) :=
  actualCostLink_transferLogBound p D (length D) (tuple D) (tuple_liesOver D)
    theta route thetaBase heightData ramification
    (data p D theta route thetaBase heightData ramification X) rfl rfl
    (volumeData p D theta route thetaBase heightData ramification X)
    (qFamily p D theta route thetaBase heightData ramification X) rfl rfl

theorem corollary312_of_transferLogBound : Corollary312 p
    (data p D theta route thetaBase heightData ramification X) := by
  exact corollary312_of_transfer_log_bound p
    (data p D theta route thetaBase heightData ramification X)
    (volumeData p D theta route thetaBase heightData ramification X)
    (qFamily p D theta route thetaBase heightData ramification X).toQFamily
    (volumeNormalization p D theta route thetaBase heightData ramification X)
    (transferLogBound p D theta route thetaBase heightData ramification X)
    D.prime.ℓ_prime D.prime.five_le (by rfl) (length_pos D)

/-- The raw completion-norm target follows from the remaining analytic laws. -/
theorem corollary312 : Corollary312 p
    (data p D theta route thetaBase heightData ramification X) :=
  raw_volume_bound D

end
end JoshiTeich.Act1Scene1.CanonicalActualHull
