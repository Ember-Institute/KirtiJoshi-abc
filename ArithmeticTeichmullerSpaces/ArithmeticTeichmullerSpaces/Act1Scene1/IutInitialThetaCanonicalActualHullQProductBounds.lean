import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullQProductNormalization

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-QPRODUCT-BOUNDS
source: the actual Tate-parameter laws and the canonical actual-hull
qFactor/qProduct definitions.
fidelity: proves strict positivity and contraction of every canonical raw
q-factor and of their finite product.
boundary: Scene1/Derived; this is an actual raw-norm sign result and does
not identify paper normalization or thetaVolume.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.QProductBounds

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

theorem qFactor_pos (i : (Target p D theta route thetaBase heightData ramification X).qIndex) :
    0 < (Volume p D theta route thetaBase heightData ramification X).qFactor i := by
  dsimp [Volume, CanonicalActualHull.volumeData]
  exact Real.rpow_pos_of_pos
    ((iutInitialThetaTateParameterData_laws D).norm_pos i.1 i.2) _

theorem qFactor_lt_one (i : (Target p D theta route thetaBase heightData ramification X).qIndex) :
    (Volume p D theta route thetaBase heightData ramification X).qFactor i < 1 := by
  dsimp [Volume, CanonicalActualHull.volumeData]
  apply Real.rpow_lt_one (norm_nonneg _)
  · exact (iutInitialThetaTateParameterData_laws D).norm_lt_one i.1 i.2
  · have hell : 0 < D.prime.ℓ := D.prime.ℓ_prime.pos
    positivity

theorem qProduct_pos :
    0 < Corollary312Data.qProduct p
      (Target p D theta route thetaBase heightData ramification X)
      (Volume p D theta route thetaBase heightData ramification X).qFactor := by
  exact corollary312_qProduct_pos p _ _ (qFactor_pos p D theta route thetaBase heightData ramification X)

theorem qProduct_lt_one :
    Corollary312Data.qProduct p
      (Target p D theta route thetaBase heightData ramification X)
      (Volume p D theta route thetaBase heightData ramification X).qFactor < 1 := by
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
      (qFactor_pos p D theta route thetaBase heightData ramification X i)
      (qFactor_lt_one p D theta route thetaBase heightData ramification X i))
  have hSum : 0 < Corollary312Data.qLogSum p T := by
    unfold Corollary312Data.qLogSum
    exact Finset.sum_pos (fun i _ => hTerm i) (by simpa using hne)
  rw [CanonicalActualHull.QProductNormalization.qProduct_eq_exp_neg_ellStar_mul_qLogSum
    p D theta route thetaBase heightData ramification X]
  rw [Real.exp_lt_one_iff]
  have hell : 0 < T.ellStar := by
    dsimp [T, CanonicalActualHull.data]
    exact length_pos D
  have hellR : (0 : ℝ) < (T.ellStar : ℝ) := by exact_mod_cast hell
  have hneg : -((T.ellStar : ℝ) * Corollary312Data.qLogSum p T) < 0 := by
    exact neg_lt_zero.mpr (mul_pos hellR hSum)
  simpa [T] using hneg

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.QProductBounds
