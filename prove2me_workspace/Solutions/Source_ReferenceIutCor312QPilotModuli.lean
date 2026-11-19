import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TatePoleOrder
import Solutions.Source_ReferenceIutQPilot
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlacesOver
import Solutions.Source_TripodPlaceUnder
import Solutions.Source_TripodRelativeAbsoluteValue
import Solutions.Source_TripodRelativeDegreeSum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve WithZero
open scoped BigOperators Classical WithZero

universe u

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The `j`-invariant viewed as an element of the moduli field. -/
noncomputable def InitialThetaData.moduliJ (D : InitialThetaData AG TG) :
    ↥(fieldOfModuli D.F D.E) :=
  ⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩

/-- At a bad place, the log norm of `j` is the Tate order times `f_w log p_w`. -/
theorem InitialThetaData.log_j_eq_qOrder (D : InitialThetaData AG TG)
    (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    Real.log (w D.E.j) =
      (D.prime.qOrder w hw : ℝ) * inertDeg D.F w * Real.log (residueChar w) := by
  let t := D.prime.tate w hw
  have hq : Valued.v (t.q : localCompletion w) = exp (-(D.prime.qOrder w hw : ℤ)) :=
    valued_tateParameter_q t (D.prime.unif_isUniformizer w hw)
  have hj : t.tateJ = FinitePlace.embedding w.maximalIdeal D.E.j := D.prime.tateJ_eq w hw
  rw [← FinitePlace.norm_embedding_eq, ← hj, t.norm_tateJ (twelve_ne_zero w),
    Tripod.norm_eq_zpow_of_valued w _ _ hq, Real.log_inv, Real.log_zpow, Real.log_pow,
    Int.cast_neg, Int.cast_natCast,
    show Tripod.inertDeg D.F w = inertDeg D.F w from rfl,
    show Tripod.residueChar w = residueChar w from rfl]
  ring

namespace QPilotInputs

variable {D : InitialThetaData AG TG} (QI : QPilotInputs D)

/-- The bad moduli places, obtained by contracting the q-pilot support. -/
noncomputable def badModuliFinset : Finset (FinitePlace ↥(fieldOfModuli D.F D.E)) :=
  QI.qPilot.badFinset.image (Tripod.placeUnder (k := ↥(fieldOfModuli D.F D.E)))

theorem mem_badModuliFinset {v : FinitePlace ↥(fieldOfModuli D.F D.E)} :
    v ∈ QI.badModuliFinset ↔ v ∈ D.VBad := by
  rw [badModuliFinset, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hwv⟩ := QI.qPilot.mem_bad hw
    rw [Tripod.placeUnder_eq_of_liesOver_place hwv]
    exact hv
  · intro hv
    obtain ⟨w, hwv⟩ := JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver (K := D.F) v
    exact ⟨w, (Set.ext_iff.mp QI.qPilot.badFinset_spec w).mpr ⟨v, hv, hwv⟩,
      Tripod.placeUnder_eq_of_liesOver_place hwv⟩

/-- Summing the complete moduli fibers gives the q-pilot log with the moduli-field degree. -/
theorem logQ_eq_moduli_jLogSum :
    QI.qPilot.logQ =
      (∑ v ∈ QI.badModuliFinset, Real.log (v D.moduliJ)) /
        (Module.finrank ℚ ↥(fieldOfModuli D.F D.E) : ℝ) := by
  let M := ↥(fieldOfModuli D.F D.E)
  let baseLog (w : FinitePlace D.F) : ℝ := Real.log (w D.E.j)
  have hbase : QI.qPilot.logQ =
      (∑ w ∈ QI.qPilot.badFinset, baseLog w) / (Module.finrank ℚ D.F : ℝ) := by
    unfold QPilotData.logQ
    rw [Finset.sum_div, ← Finset.sum_attach QI.qPilot.badFinset
      (fun w => baseLog w / (Module.finrank ℚ D.F : ℝ))]
    refine Finset.sum_congr rfl fun w _ => ?_
    change ((inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F) *
      (D.prime.qOrder w.1 (QI.qPilot.mem_bad w.2) : ℝ) * Real.log (residueChar w.1) =
        Real.log (w.1 D.E.j) / Module.finrank ℚ D.F
    rw [D.log_j_eq_qOrder w.1 (QI.qPilot.mem_bad w.2)]
    ring
  have hfibers : (∑ w ∈ QI.qPilot.badFinset, baseLog w) =
      (Module.finrank M D.F : ℝ) * ∑ v ∈ QI.badModuliFinset, Real.log (v D.moduliJ) := by
    let under : FinitePlace D.F → FinitePlace M := Tripod.placeUnder (k := M)
    have hmaps : ∀ w ∈ QI.qPilot.badFinset, under w ∈ QI.badModuliFinset :=
      fun _ hw => Finset.mem_image_of_mem under hw
    rw [← Finset.sum_fiberwise_of_maps_to hmaps baseLog, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    let fiber := QI.qPilot.badFinset.filter (fun w => under w = v)
    have hspec (w : FinitePlace D.F) : w ∈ fiber ↔ FinitePlace.LiesOver w v := by
      rw [Finset.mem_filter]
      constructor
      · intro hw
        rw [← hw.2]
        exact Tripod.liesOver_placeUnder w
      · intro hwv
        have hvBad := QI.mem_badModuliFinset.mp hv
        exact ⟨(Set.ext_iff.mp QI.qPilot.badFinset_spec w).mpr ⟨v, hvBad, hwv⟩,
          Tripod.placeUnder_eq_of_liesOver_place hwv⟩
    calc
      ∑ w ∈ fiber, baseLog w =
          ∑ w ∈ fiber, (Tripod.relLocalDeg w v : ℝ) * Real.log (v D.moduliJ) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        change Real.log (w D.E.j) = _
        have hj : algebraMap M D.F D.moduliJ = D.E.j := rfl
        rw [← hj, Tripod.apply_algebraMap_eq_pow ((hspec w).mp hw), Real.log_pow]
      _ = _ := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Tripod.sum_relLocalDeg_liesOver v fiber hspec]
  have hdegree : (Module.finrank ℚ D.F : ℝ) =
      (Module.finrank M D.F : ℝ) * (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast ((Module.finrank_mul_finrank ℚ M D.F).symm.trans (Nat.mul_comm _ _))
  have hrel : (Module.finrank M D.F : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank M D.F).ne'
  rw [hbase, hfibers, hdegree, mul_div_mul_left _ _ hrel]

/-- The signed q-pilot uses the negative bad-place `j`-log sum divided by `2ℓ[F_mod : ℚ]`. -/
theorem lhs_eq_neg_moduli_jLogSum :
    QI.qPilot.lhs =
      -((∑ v ∈ QI.badModuliFinset, Real.log (v D.moduliJ)) /
        (2 * (D.ℓ : ℝ) * (Module.finrank ℚ ↥(fieldOfModuli D.F D.E) : ℝ))) := by
  rw [QPilotData.lhs, QPilotData.absLogQ, QI.logQ_eq_moduli_jLogSum]
  ring

end QPilotInputs
end AbcAdaptation.Reference.Iut
