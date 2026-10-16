import ArithmeticTeichmullerSpaces.Act1Scene1.IutSixTorsionDivisorCard
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionDegreeOne
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionQOrderPower
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRoot

/-!
source-id: JT-SCENE1-ACTUAL-BASE-TATE-SIXTH-ROOT
source: actual rational six-torsion, split multiplicative uniformization
from rational three-torsion, and Tate j-invariant uniqueness.
fidelity: the original base-completion Tate parameter has a sixth root
on the full odd multiplicative support; its integer q-order is divisible
by six and at least six. No absolute ramification bound is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue NumberField WeierstrassCurve TateCurvesTheta
open scoped Classical Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem baseTateParameter_has_sixth_root
    (w : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    ∃ r : w.1.maximalIdeal.adicCompletion D.F,
      r ^ 6 = (iutInitialThetaOddSupportBaseQPilotSource D).tateParameter w := by
  letI : IsAlgClosure D.F D.Fbar := D.isAlgClosure
  letI : IsAlgClosed D.Fbar := D.isAlgClosure.isAlgClosed
  let K : IntermediateField D.F D.Fbar := ⊥
  letI : NumberField ↥K := NumberField.of_module_finite D.F ↥K
  letI : DecidableEq ↥K := fun a b => Classical.propDecidable (a = b)
  obtain ⟨z, hzw⟩ := JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver (K := ↥K) w.1
  have hOver : Ideal.LiesOver z.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal := hzw
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let V := iutVBadOddModSupportPort D
  have hbase : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E V := by
    dsimp only [V]
    rw [← iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D]
    rw [← iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport D]
    exact B.mem_badPlaces w
  obtain ⟨v, hv, hwv⟩ := hbase
  letI : Algebra ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) ↥K :=
    (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  letI : IsScalarTower ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F ↥K :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)
  have hbad : JoshiTeich.ReferenceIut.IsBadPlace D.E K V z :=
    ⟨v, hv, JoshiTeich.ReferenceIut.FinitePlace.liesOver_trans hzw hwv⟩
  let g := iutWeierstrassPointMap (E := D.E) (algebraMap D.F ↥K)
  let T := (iutTorsion D.E.toAffine.Point 3).map g
  have hT : T ≤ iutTorsion (D.E.map (algebraMap D.F ↥K)).toAffine.Point 3 := by
    rintro _ ⟨P, hP, rfl⟩
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp hP, map_zero]
  have hcard : 3 * 3 ≤ Nat.card T := by
    rw [← Nat.card_congr (AddSubgroup.equivMapOfInjective _ g
      (iutWeierstrassPointMap_injective _)).toEquiv]
    rw [torsion_card_of_rational_six_divisor (Fbar := D.Fbar) D.global.six_torsion_rational 3 (by decide) (by decide)]
    norm_num
  let S := JoshiTeich.ReferenceIut.tateStructureOfTorsion D.E K 3
    (fun _ h => h.1) (fun _ h => h.2.2) (by decide) (by decide) T hT hcard hbad
  let f := iutWeierstrassPointMap (E := D.E.map (algebraMap D.F ↥K))
    (FinitePlace.embedding z.maximalIdeal)
  obtain ⟨r, hr⟩ := exists_sixth_root_of_rational_six_torsion (Fbar := D.Fbar)
    (IutTateQuotientUniformization.ofTateStructure S) (f.comp g)
    ((iutWeierstrassPointMap_injective _).comp (iutWeierstrassPointMap_injective _))
    D.global.six_torsion_rational
  change r ^ 6 = (S.t.q : _) at hr
  let t := iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w.1 (B.mem_badPlaces w)
  have htJ : t.tateJ = FinitePlace.embedding w.1.maximalIdeal D.E.j :=
    iutInitialThetaOddSupportBaseTateParameterAtCurvePlace_tateJ_eq D w.1 (B.mem_badPlaces w)
  have hJ : (iutEmbedTateParameter hOver t).tateJ = S.t.tateJ := by
    rw [← iutTateJ_embed hOver t,
      htJ,
      iutEmbedCompletion_embedding, iutTateStructure_tateJ_eq, iutCurve_j_eq_div]
    simp only [JoshiTeich.ReferenceIut.curveKw, JoshiTeich.ReferenceIut.curveK,
      WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, map_div₀, map_pow]
  have hq := iutTateParameter_q_eq_of_tateJ_eq hOver t S.t hJ
  obtain ⟨r₀, hr₀⟩ := LocalCompletion.embedCompletion_surjective_of_finrank_eq_one hOver
    (show Module.finrank D.F ↥K = 1 from IntermediateField.finrank_bot) r
  refine ⟨r₀, (iutEmbedCompletion hOver).injective ?_⟩
  rw [map_pow, hr₀, hr]
  exact hq

theorem baseTateParameter_six_dvd_qOrder
    (w : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    6 ∣ (iutInitialThetaOddSupportBaseQPilotSource D).qOrder w := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  obtain ⟨r, hr⟩ := baseTateParameter_has_sixth_root D w
  exact LocalCompletion.qOrder_dvd_of_power_root w.1 (B.tateParameter w)
    (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w) 6 (by decide) r hr

theorem baseTateParameter_qOrder_ge_six
    (w : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    6 ≤ (iutInitialThetaOddSupportBaseQPilotSource D).qOrder w :=
  Nat.le_of_dvd ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder_pos w)
    (baseTateParameter_six_dvd_qOrder D w)

end
end JoshiTeich.Act1Scene1
