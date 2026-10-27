import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullSummary
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullQProductBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullSideConditions
import ArithmeticTeichmullerSpaces.Act1Scene1.VolumeBridge

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-VOLUME-SIGN
source: the canonical actual-hull volume definition and the normalized
ordinary-log hull volume bound; Joshi III 3495--3557 and 3617--3645.
fidelity: transfers positivity and the upper bound `thetaVolume ≤ 1` from
the actual generated hull to the canonical Corollary 3.12 target, then
assembles the explicit volume-bound consumer.  It does not identify this
target with the paper theta locus or construct the missing producer.
boundary: Scene1/Derived; paper theta/BK/untilt identities remain open.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.VolumeSign

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
abbrev Volume := CanonicalActualHull.volumeData p D theta route thetaBase heightData ramification X

theorem thetaVolume_le_one :
    (Target p D theta route thetaBase heightData ramification X).thetaVolume ≤ 1 := by
  rw [CanonicalActualHull.data_thetaVolume_eq p D theta route thetaBase heightData ramification X]
  exact VBadThetaLogCollation.volume_le_one D (CanonicalActualHull.length D)
    (CanonicalActualHull.tuple D) (CanonicalActualHull.tuple_liesOver D)

theorem log_thetaVolume_nonpos :
    Real.log (Target p D theta route thetaBase heightData ramification X).thetaVolume ≤ 0 := by
  exact Real.log_nonpos
    (CanonicalActualHull.SideConditions.sideConditions p D theta route thetaBase
      heightData ramification X).thetaVolume_pos.le
    (thetaVolume_le_one p D theta route thetaBase heightData ramification X)

theorem abs_log_thetaVolume_eq_neg_log :
    |Real.log (Target p D theta route thetaBase heightData ramification X).thetaVolume| =
      -Real.log (Target p D theta route thetaBase heightData ramification X).thetaVolume :=
  abs_of_nonpos (log_thetaVolume_nonpos p D theta route thetaBase heightData ramification X)

theorem volumeBound :
    Corollary312VolumeBound p (Target p D theta route thetaBase heightData ramification X)
      (Volume p D theta route thetaBase heightData ramification X) := by
  refine
    { qFactor_pos := fun i => CanonicalActualHull.QProductBounds.qFactor_pos p D theta route
        thetaBase heightData ramification X i
      qFactor_le_one := fun i =>
        (CanonicalActualHull.QProductBounds.qFactor_lt_one p D theta route thetaBase
          heightData ramification X i).le
      qLogTerm_eq := ?_
      thetaVolume_le_one := thetaVolume_le_one p D theta route thetaBase heightData ramification X
      volume_lower_bound := ?_ }
  · intro i
    rfl
  · exact CanonicalActualHull.thetaVolume_ge_qProduct p D theta route thetaBase
      heightData ramification X

theorem corollary312_of_volumeBound :
    Corollary312 p (Target p D theta route thetaBase heightData ramification X) :=
  corollary312_of_volume_lower_bound p
    (Target p D theta route thetaBase heightData ramification X)
    (CanonicalActualHull.SideConditions.sideConditions p D theta route thetaBase
      heightData ramification X)
    (Volume p D theta route thetaBase heightData ramification X)
    (volumeBound p D theta route thetaBase heightData ramification X)

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.VolumeSign
