import ArithmeticTeichmullerSpaces.Act1Scene1.AdelicThetaLinkBridge
import ArithmeticTeichmullerSpaces.Prologue.Audit.Models
import ArithmeticTeichmullerSpaces.Prologue.Audit.PerfectoidBridgeModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.TateModels

namespace JoshiTeich.Act1Scene1.Audit

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Audit
open JoshiTeich.Prologue.Theta
open scoped BigOperators NumberField

instance scene_padicTwo_not_unit : Fact (¬ IsUnit (2 : ℤ_[2])) :=
  padicTwo_not_unit
noncomputable instance scene_padicTwo_is_adic_complete :
    IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
  padicTwo_is_adic_complete

section SceneInstances

local instance scene_local_padicTwo_not_unit : Fact (¬ IsUnit (2 : ℤ_[2])) :=
  scene_padicTwo_not_unit
local instance scene_local_padicTwo_is_adic_complete :
    IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
  scene_padicTwo_is_adic_complete

noncomputable def sceneTateData : TateParameterData ℚ where
  places := {rationalTwoPlace}
  parameter := fun _ => 16
  norm := fun w => w (16 : ℚ)

theorem sceneTateData_laws : TateParameterLaws sceneTateData := by
  constructor
  · simp [sceneTateData]
  · intro w hw
    norm_num [sceneTateData]
  · intro w hw
    rfl
  · intro w hw
    exact NumberField.FinitePlace.pos_iff.mpr (by norm_num [sceneTateData])
  · intro w hw
    simp only [sceneTateData, Finset.mem_singleton] at hw ⊢
    subst w
    change ‖NumberField.FinitePlace.embedding rationalTwoHeightOne (16 : ℚ)‖ < 1
    have hnorm :
        ‖NumberField.FinitePlace.embedding rationalTwoHeightOne
            (algebraMap (𝓞 ℚ) ℚ (16 : 𝓞 ℚ))‖ < 1 :=
      (NumberField.FinitePlace.norm_lt_one_iff_mem ℚ rationalTwoHeightOne
        (16 : 𝓞 ℚ)).2 (by
          change (16 : 𝓞 ℚ) ∈ rationalTwoPrimeIdeal
          change Rat.ringOfIntegersEquiv (16 : 𝓞 ℚ) ∈ Ideal.span {(2 : ℤ)}
          have hmap : Rat.ringOfIntegersEquiv (16 : 𝓞 ℚ) = (16 : ℤ) := by
            apply Rat.ringOfIntegersEquiv.symm.injective
            apply NumberField.RingOfIntegers.ext
            simp [Rat.ringOfIntegersEquiv_apply_coe]
          rw [hmap]
          exact Ideal.mem_span_singleton.mpr (by norm_num))
    have hmap : algebraMap (𝓞 ℚ) ℚ (16 : 𝓞 ℚ) = (16 : ℚ) := by
      exact map_natCast (algebraMap (𝓞 ℚ) ℚ) 16
    rw [hmap] at hnorm
    exact hnorm

noncomputable def sceneQNorm : ℝ := sceneTateData.norm rationalTwoPlace

noncomputable def sceneQFactor : ℝ := sceneQNorm ^ (1 / 4 : ℝ)

noncomputable def sceneQTerm : ℝ := -Real.log sceneQFactor

theorem sceneQNorm_pos : 0 < sceneQNorm := by
  exact sceneTateData_laws.norm_pos rationalTwoPlace (by simp [sceneTateData])

theorem sceneQNorm_lt_one : sceneQNorm < 1 := by
  exact sceneTateData_laws.norm_lt_one rationalTwoPlace (by simp [sceneTateData])

theorem sceneQFactor_pos : 0 < sceneQFactor := by
  unfold sceneQFactor
  exact Real.rpow_pos_of_pos sceneQNorm_pos _

theorem sceneQFactor_lt_one : sceneQFactor < 1 := by
  unfold sceneQFactor
  apply Real.rpow_lt_one sceneQNorm_pos.le sceneQNorm_lt_one
  norm_num

theorem sceneQTerm_pos : 0 < sceneQTerm := by
  unfold sceneQTerm
  exact neg_pos.mpr (Real.log_neg sceneQFactor_pos sceneQFactor_lt_one)

theorem sceneQTerm_ne_zero : sceneQTerm ≠ 0 := sceneQTerm_pos.ne'

/- A concrete theta pilot with positive log-shell and matching volume. -/
noncomputable def sceneTheta : ThetaPilotData ℚ where
  index := Fin 2
  indexFintype := inferInstance
  value := fun _ => 2
  norm := fun _ => Real.exp sceneQTerm
  scalingIndex := fun _ => 1
  frobenius := fun i => i
  period := fun _ => sceneQTerm
  liftedLog := fun _ => sceneQTerm

theorem sceneTheta_scaling_laws :
    ThetaPilotScalingLaws sceneTheta (0 : Fin 2) := by
  refine ⟨by rfl, ?_, ?_, ?_⟩
  · intro i
    change (2 : ℚ) ≠ 0
    norm_num
  · intro i
    change 0 < Real.exp sceneQTerm
    exact Real.exp_pos _
  · intro i
    change Real.exp sceneQTerm = (Real.exp sceneQTerm) ^ (1 * 1)
    norm_num

noncomputable def scenePacketHull : PacketHullData (Fin 2) where
  packet := Fin 1
  packetFintype := inferInstance
  packetToPilot := fun _ => 0
  packetWeight := fun _ => sceneQTerm
  hull := Fin 1
  hullFintype := inferInstance
  hullToPacket := fun _ => 0
  hullWeight := fun _ => sceneQTerm

noncomputable def sceneLinkData : AdelicThetaLinkData ℚ :=
  AdelicThetaLinkData.ofTateParameters sceneTateData sceneTheta (0 : Fin 2)
    scenePacketHull auditHeight auditRamificationProfile (2 * sceneQTerm) 1

theorem sceneLink_tate_compatibility :
    QNormTateCompatibility sceneLinkData := by
  exact qNormTateCompatibility_of_tateParameters sceneTateData sceneTheta
    (0 : Fin 2) scenePacketHull auditHeight auditRamificationProfile
    (2 * sceneQTerm) 1

theorem sceneLink_first_axiom : FirstAxiom sceneLinkData := by
  constructor
  · simp [sceneLinkData, AdelicThetaLinkData.ofTateParameters, sceneTateData]
  · intro w hw
    have hwTate : w ∈ sceneTateData.places := by
      simpa [sceneLinkData, AdelicThetaLinkData.ofTateParameters] using hw
    change sceneTateData.parameter w ≠ 0
    exact sceneTateData_laws.parameter_nonzero w hwTate
  · intro w hw
    change 0 < w (16 : ℚ)
    exact NumberField.FinitePlace.pos_iff.mpr (by norm_num)
  · intro x
    exact auditHeight_nonneg x
  · intro i
    change 0 < Real.exp sceneQTerm
    exact Real.exp_pos _
  · intro p
    exact sceneQTerm_pos
  · intro h
    exact sceneQTerm_pos

theorem sceneLink_model : AdelicThetaLink sceneLinkData := by
  constructor
  · intro w hw j
    change w (16 : ℚ) ^ (j * j) = w ((16 : ℚ) ^ (j * j))
    exact (map_pow w (16 : ℚ) (j * j)).symm
  · exact sceneTheta_scaling_laws
  · intro i
    rfl
  · change 2 * sceneQTerm = ∑ _ : Fin 2, sceneQTerm
    simp [Fin.sum_univ_succ]

theorem sceneThetaLiftLog_model : ThetaLiftLog sceneLinkData := by
  constructor
  · intro i
    change sceneQTerm = Real.log (Real.exp sceneQTerm)
    rw [Real.log_exp]
  · intro i
    change (2 : ℚ) ≠ 0
    norm_num

theorem scenePacketCollationHull_model : PacketCollationHull sceneLinkData := by
  constructor
  · intro p
    change (0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2))
    simp
  · intro h
    change (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1))
    simp
  · intro p
    change sceneQTerm ≠ 0
    exact sceneQTerm_ne_zero
  · intro h
    change sceneQTerm ≠ 0
    exact sceneQTerm_ne_zero

theorem sceneVolumeTransfer_model : VolumeTransfer sceneLinkData := by
  constructor
  change 2 * sceneQTerm =
    (∑ _ : Fin 1, sceneQTerm) + ∑ _ : Fin 1, sceneQTerm
  simp [Fin.sum_univ_succ]
  ring

noncomputable def scenePlaceData :
    @PerfectoidPlaceData ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete :=
  padicTwoPlaceData

noncomputable def sceneBridgeData :
    @PerfectoidBridgeData ℚ inferInstance inferInstance sceneLinkData
      ℤ_[2] inferInstance 2 inferInstance scene_padicTwo_not_unit
      scene_padicTwo_is_adic_complete scenePlaceData :=
  @PerfectoidBridgeData.mk ℚ inferInstance inferInstance sceneLinkData
    ℤ_[2] inferInstance 2 inferInstance scene_padicTwo_not_unit
    scene_padicTwo_is_adic_complete scenePlaceData padicTwoIntegralMap

noncomputable def sceneInputData :
    @PrologueInputData ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete :=
  @PrologueInputData.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete
    sceneLinkData scenePlaceData sceneBridgeData

theorem sceneInput_laws :
    @PrologueInputLaws ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneInputData := by
  have hlocal :
      @PerfectoidPlaceLaws ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
        inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete scenePlaceData :=
    @PerfectoidPlaceLaws.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete scenePlaceData
      (by
        change @Perfectoid.PerfectoidLaws ℤ_[2] inferInstance 2 inferInstance
          padicTwo_not_unit padicTwoPerfectoidData
        exact padicTwo_perfectoid_model)
  have hbridge :
      @PerfectoidBridgeLaws ℚ inferInstance inferInstance sceneLinkData
        ℤ_[2] inferInstance 2 inferInstance scene_padicTwo_not_unit
        scene_padicTwo_is_adic_complete scenePlaceData sceneBridgeData :=
    @PerfectoidBridgeLaws.mk ℚ inferInstance inferInstance sceneLinkData
      ℤ_[2] inferInstance 2 inferInstance scene_padicTwo_not_unit
      scene_padicTwo_is_adic_complete scenePlaceData sceneBridgeData
      (by
        simp [scenePlaceData, padicTwoPlaceData, sceneLinkData,
          AdelicThetaLinkData.ofTateParameters, sceneTateData]) hlocal
  exact @PrologueInputLaws.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete
    sceneInputData sceneLink_first_axiom sceneTateData_laws sceneLink_model hbridge

noncomputable def sceneInput :
    @Scene1Input ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete :=
  @Scene1Input.ofExplicit ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete
    sceneInputData sceneInput_laws sceneLink_model sceneThetaLiftLog_model
    scenePacketCollationHull_model sceneVolumeTransfer_model

noncomputable def sceneTarget :
    @Corollary312Data ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete :=
  @Corollary312Data.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete
    sceneInput 2 2 (Fin 1) inferInstance (fun _ => sceneQTerm)
    (Real.exp (-2 * sceneQTerm))

noncomputable def sceneVolume :
    @Corollary312VolumeData ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget :=
  @Corollary312VolumeData.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget
    (fun _ => sceneQFactor)

theorem sceneTarget_link_eq :
    letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
    letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
      scene_padicTwo_is_adic_complete
    sceneTarget.scene1.data.link = sceneLinkData := by
  rfl

noncomputable def sceneSourcePlace :
    @Corollary312SourceQIndex ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget :=
  ⟨rationalTwoPlace, by
    letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
    letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
      scene_padicTwo_is_adic_complete
    change rationalTwoPlace ∈ sceneTarget.scene1.data.link.places
    rw [sceneTarget_link_eq]
    simp [sceneLinkData, AdelicThetaLinkData.ofTateParameters, sceneTateData]⟩

theorem scene_qFactor_source :
    @Corollary312SourceQFactor ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget sceneSourcePlace =
      sceneQFactor := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  unfold Corollary312SourceQFactor sceneQFactor sceneQNorm
  change (sceneTarget.scene1.data.link.qNorm sceneSourcePlace.1) ^
      (1 / (2 * (sceneTarget.ell : ℝ))) =
    (sceneTateData.norm rationalTwoPlace) ^ (1 / 4 : ℝ)
  change (sceneLinkData.qNorm rationalTwoPlace) ^
      (1 / (2 * (sceneTarget.ell : ℝ))) =
    (sceneTateData.norm rationalTwoPlace) ^ (1 / 4 : ℝ)
  congr 1 <;> norm_num [sceneTarget, sceneLinkData, sceneTateData]

noncomputable def scene_qFamily :
    @Corollary312QFamily ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget sceneVolume := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  letI := sceneTarget.qIndexFintype
  let qZero : sceneTarget.qIndex := by
    change Fin 1
    exact 0
  let iEquiv : sceneTarget.qIndex ≃
      @Corollary312SourceQIndex ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
        inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget :=
    { toFun := fun _ => sceneSourcePlace
      invFun := fun _ => qZero
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by
        intro i
        apply Subtype.ext
        have hi : i.1 = rationalTwoPlace := by
          have hiProp := i.property
          change i.1 ∈ sceneLinkData.places at hiProp
          simpa [sceneLinkData, AdelicThetaLinkData.ofTateParameters, sceneTateData]
            using hiProp
        exact hi.symm }
  exact Corollary312QFamily.ofTateCompatibility 2 sceneTarget sceneVolume
    sceneLink_tate_compatibility iEquiv
    (by
      intro i
      fin_cases i
      change sceneQFactor =
        Corollary312SourceQFactor 2 sceneTarget sceneSourcePlace
      exact scene_qFactor_source.symm)
    (by
      intro i
      fin_cases i
      change sceneQTerm =
        -Real.log (Corollary312SourceQFactor 2 sceneTarget sceneSourcePlace)
      rw [scene_qFactor_source]
      rfl)

theorem scene_normalization :
    @Corollary312VolumeNormalization ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  constructor
  change sceneTarget.thetaVolume =
    Real.exp (-sceneTarget.scene1.data.link.logVolume)
  rw [sceneTarget_link_eq]
  simpa [sceneTarget, sceneLinkData, AdelicThetaLinkData.ofTateParameters]

noncomputable def scene_accounting :
    @Corollary312TransferQAccounting ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  letI := sceneTarget.qIndexFintype
  let qZero : sceneTarget.qIndex := by
    change Fin 1
    exact 0
  let f : sceneLinkData.packetHull.packet → sceneTarget.qIndex := fun _ => qZero
  let g : sceneLinkData.packetHull.hull → sceneTarget.qIndex := fun _ => qZero
  exact
    { packet_qIndex := f
      hull_qIndex := g
      packet_weight_le_qLogTerm := by
        intro x
        change sceneQTerm ≤ sceneQTerm
        exact le_rfl
      hull_weight_le_qLogTerm := by
        intro x
        change sceneQTerm ≤ sceneQTerm
        exact le_rfl
      q_accounting := by
        change (∑ _ : Fin 1, sceneQTerm) + ∑ _ : Fin 1, sceneQTerm =
          (2 : ℝ) * ∑ _ : Fin 1, sceneQTerm
        ring }

noncomputable def sceneData :
    @Corollary312Scene1Data ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  exact
    { target := sceneTarget
      volume := sceneVolume
      qFamily := scene_qFamily
      normalization := scene_normalization
      accounting := scene_accounting
      ell_prime := by exact Nat.prime_two
      ellStar_pos := by norm_num [sceneTarget] }

theorem scene_satisfying_model :
    @Corollary312 ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  simpa [sceneData] using (cor312_of_adelicThetaLink 2 sceneData)

noncomputable def sceneBadTarget :
    @Corollary312Data ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete :=
  by
    letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
    letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
      scene_padicTwo_is_adic_complete
    exact { sceneTarget with thetaVolume := 0 }

theorem scene_bad_normalization_violation :
    letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
    letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
      scene_padicTwo_is_adic_complete
    ¬ @Corollary312VolumeNormalization ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneBadTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  intro h
  have heq := h.thetaVolume_eq_exp_neg_logVolume
  change (0 : ℝ) = Real.exp (-sceneBadTarget.scene1.data.link.logVolume) at heq
  have hpos : 0 < Real.exp (-sceneBadTarget.scene1.data.link.logVolume) :=
    Real.exp_pos _
  linarith

end SceneInstances

end JoshiTeich.Act1Scene1.Audit
