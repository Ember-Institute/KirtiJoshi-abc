import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogSingletonCriterion
import ArithmeticTeichmullerSpaces.Act1Scene1.Corollary312

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-REFERENCE-MARGIN
source: the formal Corollary 3.12 target, actual ordinary-log hull volume,
and the exact reference q-pilot value; Joshi III 3617--3650.
fidelity: for an actual ordinary collation, after identifying the target
volume and q-sum, the Corollary inequality is equivalent to correctedCost
being at most the actual reference absLogQ. The selected paper sum is a
strictly larger intermediary and cannot replace this condition.
This module does not assert the reference-margin sign.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (T : Corollary312Data (K := D.F) (O := O) p)
local instance referenceMarginPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
variable (n : ℕ)


theorem corollary312_iff_actual_reference_margin
    (hn : 0 < n)
    (hellStar : T.ellStar = n)
    (hvolume : T.thetaVolume =
      FullSupportWitnessHull.volume D n (ordinarySingletonCollation D n))
    (hq : Corollary312Data.qLogSum p T =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D)) :
    Corollary312 p T ↔
      FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) ≤
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [Corollary312, hq, hellStar, hvolume]
  rw [ordinarySingletonCollation_volume_eq D n]
  have havg := ordinary_averageAbsLog_eq_correctedCost D n hn
  have havgNeg : -(1 / (n : ℝ)) * |Real.log (volume D n)| =
      -(FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1)) := by
    linarith [havg]
  rw [havgNeg]
  constructor <;> intro h <;> linarith [h]

theorem not_corollary312_of_actual_reference_margin_negative
    (hn : 0 < n)
    (hellStar : T.ellStar = n)
    (hvolume : T.thetaVolume =
      FullSupportWitnessHull.volume D n (ordinarySingletonCollation D n))
    (hq : Corollary312Data.qLogSum p T =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D))
    (hneg : JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) <
      FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1)) :
    ¬ Corollary312 p T := by
  intro h
  exact (not_le_of_gt hneg)
    ((corollary312_iff_actual_reference_margin D p T n hn hellStar hvolume hq).mp h)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
