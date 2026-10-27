import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullQProductBounds

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-QLOGSUM-SIGN
source: the canonical actual-hull qFactor bounds and Corollary 3.12
qLogSum definition.
fidelity: proves strict positivity of the raw canonical qLogSum directly
from the contracting q-factors and nonempty actual Tate-place index.
boundary: Scene1/Derived; paper sign conventions and cross-normalization
remain open.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.QLogSumSign

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

theorem qLogSum_pos :
    0 < Corollary312Data.qLogSum p
      (Target p D theta route thetaBase heightData ramification X) := by
  let T := Target p D theta route thetaBase heightData ramification X
  let V := Volume p D theta route thetaBase heightData ramification X
  letI := T.qIndexFintype
  have hne : (Finset.univ : Finset T.qIndex).Nonempty := by
    obtain ⟨w, hw⟩ := (iutInitialThetaTateParameterData_laws D).places_nonempty
    exact ⟨⟨w, hw⟩, Finset.mem_univ _⟩
  have hTerm : ∀ i : T.qIndex, 0 < T.qLogTerm i := by
    intro i
    dsimp [T, CanonicalActualHull.data]
    exact neg_pos.mpr (Real.log_neg
      (CanonicalActualHull.QProductBounds.qFactor_pos p D theta route thetaBase
        heightData ramification X i)
      (CanonicalActualHull.QProductBounds.qFactor_lt_one p D theta route thetaBase
        heightData ramification X i))
  unfold Corollary312Data.qLogSum
  exact Finset.sum_pos (fun i _ => hTerm i) (by simpa using hne)

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.QLogSumSign
