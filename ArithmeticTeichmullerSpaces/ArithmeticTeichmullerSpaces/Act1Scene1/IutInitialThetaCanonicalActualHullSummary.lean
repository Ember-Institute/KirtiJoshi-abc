import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullData

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-SUMMARY
source: the actual arithmetic/Haar hull carrier and its established
normalization, q-product, transfer, and conditional Corollary 3.12 consumers.
fidelity: packages only the already proved consequences of one explicit
analytic input into a single summary proposition. It does not manufacture
that analytic input or identify it with the paper theta locus.
boundary: Scene1/Derived; paper representative, H¹ₑ/BK identity, and global
producer obligations remain open.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.Summary

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O]
variable (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (theta : ThetaPilotData D.F)
variable (route : CanonicalActualHull.PositivePacket D → theta.index)
variable (thetaBase : theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (X : CanonicalActualHull.AnalyticInput (O := O) p D theta route thetaBase
  heightData ramification)

local instance selectedPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩

abbrev Target := CanonicalActualHull.data p D theta route thetaBase heightData ramification X
abbrev QVolume := CanonicalActualHull.volumeData p D theta route thetaBase heightData ramification X
abbrev QFamily := CanonicalActualHull.qFamily p D theta route thetaBase heightData ramification X

structure Data : Prop where
  link_eq : (Target p D theta route thetaBase heightData ramification X).scene1.data.link =
    CanonicalActualHull.link D theta route thetaBase heightData ramification
  thetaVolume_eq : (Target p D theta route thetaBase heightData ramification X).thetaVolume =
    CanonicalActualHull.hullVolume D
  thetaVolume_ge_qProduct :
    (Target p D theta route thetaBase heightData ramification X).thetaVolume ≥
      Corollary312Data.qProduct p
        (Target p D theta route thetaBase heightData ramification X)
        (QVolume p D theta route thetaBase heightData ramification X).qFactor
  volumeNormalization : Corollary312VolumeNormalization p
    (Target p D theta route thetaBase heightData ramification X)
  transferLogBound : Corollary312TransferLogBound p
    (Target p D theta route thetaBase heightData ramification X)
  conditionalCorollary : Corollary312 p
    (Target p D theta route thetaBase heightData ramification X)

theorem ofCanonicalActualHull :
    Data p D theta route thetaBase heightData ramification X := by
  refine
    { link_eq := CanonicalActualHull.data_link_eq p D theta route thetaBase heightData ramification X
      thetaVolume_eq := CanonicalActualHull.data_thetaVolume_eq p D theta route thetaBase heightData ramification X
      thetaVolume_ge_qProduct := CanonicalActualHull.thetaVolume_ge_qProduct p D theta route thetaBase heightData ramification X
      volumeNormalization := CanonicalActualHull.volumeNormalization p D theta route thetaBase heightData ramification X
      transferLogBound := CanonicalActualHull.transferLogBound p D theta route thetaBase heightData ramification X
      conditionalCorollary := CanonicalActualHull.corollary312_of_transferLogBound p D theta route thetaBase heightData ramification X }

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.Summary
