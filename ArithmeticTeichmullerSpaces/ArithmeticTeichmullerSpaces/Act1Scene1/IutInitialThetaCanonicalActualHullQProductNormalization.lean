import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullData
import ArithmeticTeichmullerSpaces.Act1Scene1.Corollary312QProductAccounting

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-QPRODUCT-NORMALIZATION
source: `cor:cor312` q-product accounting and the canonical actual-hull
qFactor/qLogTerm definitions.
fidelity: proves the exact exponential normalization of the q-product for
the actual canonical target. The result is internal to the current target
and does not identify it with the paper theta-volume normalization.
boundary: Scene1/Derived; paper normalization and representative identities
remain explicit obligations.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.QProductNormalization

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

theorem qProduct_eq_exp_neg_ellStar_mul_qLogSum :
    Corollary312Data.qProduct p (Target p D theta route thetaBase heightData ramification X)
        (Volume p D theta route thetaBase heightData ramification X).qFactor =
      Real.exp (-((Target p D theta route thetaBase heightData ramification X).ellStar : ℝ) *
        Corollary312Data.qLogSum p (Target p D theta route thetaBase heightData ramification X)) := by
  let T := Target p D theta route thetaBase heightData ramification X
  let V := Volume p D theta route thetaBase heightData ramification X
  letI := T.qIndexFintype
  have hPos : ∀ i, 0 < V.qFactor i := by
    intro i
    dsimp [V, Volume, CanonicalActualHull.volumeData]
    exact Real.rpow_pos_of_pos
      ((iutInitialThetaTateParameterData_laws D).norm_pos i.1 i.2) _
  have hSum : Corollary312Data.qLogSum p T = ∑ i, -Real.log (V.qFactor i) := by
    unfold Corollary312Data.qLogSum
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  have hNeg := corollary312_negLog_qProduct_eq_ellStar_mul_sum_negLog p T V.qFactor hPos
  rw [← hSum] at hNeg
  have hLog : Real.log (Corollary312Data.qProduct p T V.qFactor) =
      -((T.ellStar : ℝ) * Corollary312Data.qLogSum p T) := by
    linarith
  have hProductPos := corollary312_qProduct_pos p T V.qFactor hPos
  have hMain : Corollary312Data.qProduct p T V.qFactor =
      Real.exp (-((T.ellStar : ℝ) * Corollary312Data.qLogSum p T)) := by
    calc
    Corollary312Data.qProduct p T V.qFactor =
        Real.exp (Real.log (Corollary312Data.qProduct p T V.qFactor)) :=
      (Real.exp_log hProductPos).symm
    _ = Real.exp (-((T.ellStar : ℝ) * Corollary312Data.qLogSum p T)) := by rw [hLog]
  simpa [T, V] using hMain

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.QProductNormalization
