import ArithmeticTeichmullerSpaces.Act1Scene1.AdelicThetaLinkBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotBridge
import ArithmeticTeichmullerSpaces.Prologue.Audit.Models
import ArithmeticTeichmullerSpaces.Prologue.Audit.PerfectoidBridgeModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.TateModels

namespace JoshiTeich.Act1Scene1.Audit

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Audit
open JoshiTeich.Prologue.Theta
open scoped BigOperators NumberField NNReal

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

/-! Arithmetic facts for the explicit `ℚ,(2)` carrier.  These facts make the
q-pilot normalization use the actual `inertDeg / [K : ℚ]` weight rather than
choosing a weight from the desired logarithmic equality. -/

theorem rationalTwoPlace_residueChar :
    Arithmetic.residueChar rationalTwoPlace = 2 := by
  have hmem : (2 : 𝓞 ℚ) ∈ rationalTwoPlace.maximalIdeal.asIdeal := by
    change (2 : 𝓞 ℚ) ∈ (NumberField.FinitePlace.mk rationalTwoHeightOne).maximalIdeal.asIdeal
    rw [NumberField.FinitePlace.maximalIdeal_mk]
    change (2 : 𝓞 ℚ) ∈ rationalTwoPrimeIdeal
    change Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) ∈ Ideal.span {(2 : ℤ)}
    have hmap : Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) = (2 : ℤ) := by
      apply Rat.ringOfIntegersEquiv.symm.injective
      apply NumberField.RingOfIntegers.ext
      simp [Rat.ringOfIntegersEquiv_apply_coe]
    rw [hmap]
    exact Ideal.mem_span_singleton_self _
  exact
    (Arithmetic.natCast_mem_maximalIdeal_iff rationalTwoPlace Nat.prime_two).mp hmem

theorem rationalTwoPlace_inertDeg :
    Arithmetic.inertDeg rationalTwoPlace = 1 := by
  let I : Ideal ℤ := Ideal.span {(2 : ℤ)}
  let P : Ideal (𝓞 ℚ) := rationalTwoPrimeIdeal
  have hIprime : I.IsPrime := by
    dsimp [I]
    exact intTwoPrimeIdeal_isPrime
  have hImax : I.IsMaximal := IsPrime.to_maximal_ideal (by
    dsimp [I]
    rw [Ideal.span_singleton_eq_bot]
    norm_num)
  letI : I.IsMaximal := hImax
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact Ideal.comap_isPrime Rat.ringOfIntegersEquiv.toRingHom I
  have hPmax : P.IsMaximal := by
    dsimp [P, rationalTwoPrimeIdeal]
    exact Ideal.comap_isMaximal_of_surjective _ Rat.ringOfIntegersEquiv.surjective
  have hmap : P.map Rat.ringOfIntegersEquiv.toRingHom = I := by
    dsimp [P, rationalTwoPrimeIdeal, I]
    exact Ideal.map_comap_of_surjective _ Rat.ringOfIntegersEquiv.surjective _
  have hOver : P.LiesOver I := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    change I = P.comap (algebraMap ℤ (𝓞 ℚ))
    ext z
    change z ∈ I ↔ Rat.ringOfIntegersEquiv (algebraMap ℤ (𝓞 ℚ) z) ∈ I
    have hz : Rat.ringOfIntegersEquiv (algebraMap ℤ (𝓞 ℚ) z) = z := by
      apply Rat.ringOfIntegersEquiv.symm.injective
      apply NumberField.RingOfIntegers.ext
      simp [Rat.ringOfIntegersEquiv_symm_apply_coe]
    rw [hz]
  letI : I.IsPrime := hIprime
  letI : P.IsPrime := hPprime
  letI : P.IsMaximal := hPmax
  letI : P.LiesOver I := hOver
  have hfin : Module.finrank (ℤ ⧸ I) (𝓞 ℚ ⧸ P) = 1 := by
    let j : (𝓞 ℚ ⧸ P) ≃+* (ℤ ⧸ I) :=
      Ideal.quotientEquiv P I Rat.ringOfIntegersEquiv hmap.symm
    have hc :
        (algebraMap (ℤ ⧸ I) (ℤ ⧸ I)).comp (RingEquiv.refl (ℤ ⧸ I)).toRingHom =
          j.toRingHom.comp (algebraMap (ℤ ⧸ I) (𝓞 ℚ ⧸ P)) := by
      ext x
      simp [j, Ideal.quotientEquiv_mk]
    have hdim := Algebra.finrank_eq_of_equiv_equiv
      (RingEquiv.refl (ℤ ⧸ I)) j hc
    simpa using hdim
  have hdeg := Ideal.inertiaDeg_eq_of_isMaximal I P
  unfold Arithmetic.inertDeg
  rw [show rationalTwoPlace.maximalIdeal.asIdeal = P by
    change (NumberField.FinitePlace.mk rationalTwoHeightOne).maximalIdeal.asIdeal = P
    rw [NumberField.FinitePlace.maximalIdeal_mk]
    rfl]
  rw [hdeg, hfin]

theorem rationalTwoPlace_two : rationalTwoPlace (2 : ℚ) = (1 / 2 : ℝ) := by
  change ‖NumberField.FinitePlace.embedding rationalTwoHeightOne (2 : ℚ)‖ = (1 / 2 : ℝ)
  rw [show (2 : ℚ) = algebraMap (𝓞 ℚ) ℚ (2 : 𝓞 ℚ) by
    exact (map_natCast (algebraMap (𝓞 ℚ) ℚ) 2).symm]
  rw [NumberField.FinitePlace.norm_embedding_int]
  have hideal : rationalTwoHeightOne.asIdeal = Ideal.span {(2 : 𝓞 ℚ)} := by
    change rationalTwoPrimeIdeal = Ideal.span {(2 : 𝓞 ℚ)}
    ext x
    change Rat.ringOfIntegersEquiv x ∈ Ideal.span {(2 : ℤ)} ↔
      x ∈ Ideal.span {(2 : 𝓞 ℚ)}
    constructor
    · intro hx
      rw [Ideal.mem_span_singleton] at hx ⊢
      obtain ⟨z, hz⟩ := hx
      have hx' : x = (2 : 𝓞 ℚ) * Rat.ringOfIntegersEquiv.symm z := by
        apply Rat.ringOfIntegersEquiv.injective
        rw [map_mul]
        have htwo : Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) = (2 : ℤ) := by
          apply Rat.ringOfIntegersEquiv.symm.injective
          apply NumberField.RingOfIntegers.ext
          simp [Rat.ringOfIntegersEquiv_apply_coe]
        rw [htwo]
        simpa using hz
      rw [hx']
      exact ⟨Rat.ringOfIntegersEquiv.symm z, rfl⟩
    · intro hx
      rw [Ideal.mem_span_singleton] at hx ⊢
      obtain ⟨z, hz⟩ := hx
      have hz' : Rat.ringOfIntegersEquiv x =
          (2 : ℤ) * Rat.ringOfIntegersEquiv z := by
        rw [hz, map_mul]
        have htwo : Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) = (2 : ℤ) := by
          apply Rat.ringOfIntegersEquiv.symm.injective
          apply NumberField.RingOfIntegers.ext
          simp [Rat.ringOfIntegersEquiv_apply_coe]
        rw [htwo]
      exact ⟨Rat.ringOfIntegersEquiv z, hz'⟩
  have hval : rationalTwoHeightOne.intValuation (2 : 𝓞 ℚ) =
      WithZero.exp (-1 : ℤ) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
      (v := rationalTwoHeightOne) (r := (2 : 𝓞 ℚ)) (by norm_num) hideal
  rw [hval, WithZeroMulInt.toNNReal_neg_apply]
  · have habs : Ideal.absNorm rationalTwoHeightOne.asIdeal = 2 := by
      change Ideal.absNorm rationalTwoPrimeIdeal = 2
      rw [show rationalTwoPrimeIdeal = Ideal.span {(2 : 𝓞 ℚ)} by exact hideal]
      have hnorm := Ideal.absNorm_span_natCast (S := 𝓞 ℚ) 2
      norm_num [NumberField.RingOfIntegers.rank] at hnorm ⊢
      exact hnorm
    change ((Ideal.absNorm rationalTwoHeightOne.asIdeal : ℝ≥0) ^ (-1 : ℤ) : ℝ) =
      (1 / 2 : ℝ)
    rw [habs]
    norm_num
  · simp

noncomputable def sceneTateData : TateParameterData ℚ where
  places := {rationalTwoPlace}
  parameter := fun _ => 16
  norm := fun w => w (16 : ℚ)
  orderNat := fun _ => 4

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
  · intro w hw
    simp [sceneTateData]

noncomputable def sceneQNorm : ℝ := sceneTateData.norm rationalTwoPlace

noncomputable def sceneQFactor : ℝ := sceneQNorm ^ (1 / 10 : ℝ)

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

noncomputable def scene_tate_order_compatibility :
    TateOrderNormCompatibility sceneLinkData := by
  refine
    { uniformizerNorm := fun w => w (2 : ℚ)
      uniformizerNorm_pos := ?_
      uniformizerNorm_lt_one := ?_
      norm_eq_pow_order := ?_ }
  · intro w hw
    simp only [sceneLinkData, AdelicThetaLinkData.ofTateParameters,
      sceneTateData, Finset.mem_singleton] at hw
    subst w
    exact NumberField.FinitePlace.pos_iff.mpr (by norm_num)
  · intro w hw
    simp only [sceneLinkData, AdelicThetaLinkData.ofTateParameters,
      sceneTateData, Finset.mem_singleton] at hw
    subst w
    change ‖NumberField.FinitePlace.embedding rationalTwoHeightOne (2 : ℚ)‖ < 1
    have hnorm :
        ‖NumberField.FinitePlace.embedding rationalTwoHeightOne
            (algebraMap (𝓞 ℚ) ℚ (2 : 𝓞 ℚ))‖ < 1 :=
      (NumberField.FinitePlace.norm_lt_one_iff_mem ℚ rationalTwoHeightOne
        (2 : 𝓞 ℚ)).2 (by
          change (2 : 𝓞 ℚ) ∈ rationalTwoPrimeIdeal
          change Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) ∈ Ideal.span {(2 : ℤ)}
          have hmap : Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) = (2 : ℤ) := by
            apply Rat.ringOfIntegersEquiv.symm.injective
            apply NumberField.RingOfIntegers.ext
            simp [Rat.ringOfIntegersEquiv_apply_coe]
          rw [hmap]
          exact Ideal.mem_span_singleton_self _)
    have hmap : algebraMap (𝓞 ℚ) ℚ (2 : 𝓞 ℚ) = (2 : ℚ) := by
      exact map_natCast (algebraMap (𝓞 ℚ) ℚ) 2
    rw [hmap] at hnorm
    exact hnorm
  · intro w hw
    simp only [sceneLinkData, AdelicThetaLinkData.ofTateParameters,
      sceneTateData, Finset.mem_singleton] at hw
    subst w
    change rationalTwoPlace (16 : ℚ) =
      (rationalTwoPlace (2 : ℚ)) ^ (4 : ℕ)
    rw [show (16 : ℚ) = (2 : ℚ) ^ (4 : ℕ) by norm_num, map_pow]

theorem sceneLink_tate_compatibility :
    QNormTateCompatibility sceneLinkData := by
  exact qNormTateCompatibility_of_tateParameters sceneTateData sceneTheta
    (0 : Fin 2) scenePacketHull auditHeight auditRamificationProfile
    (2 * sceneQTerm) 1

theorem scene_qNorm_log_eq_order_mul :
    -Real.log sceneQNorm =
      (4 : ℝ) *
        -Real.log (scene_tate_order_compatibility.uniformizerNorm rationalTwoPlace) := by
  have hw : rationalTwoPlace ∈ sceneLinkData.places := by
    simp [sceneLinkData, AdelicThetaLinkData.ofTateParameters, sceneTateData]
  have hqNorm : sceneLinkData.qNorm rationalTwoPlace = sceneQNorm := by
    rw [sceneLink_tate_compatibility.norm_eq sceneLinkData sceneTateData_laws
      rationalTwoPlace hw]
    rfl
  have h := TateOrderNormCompatibility.qNorm_log_eq_order_mul
    sceneLinkData sceneTateData_laws sceneLink_tate_compatibility
      scene_tate_order_compatibility rationalTwoPlace hw
  rw [hqNorm] at h
  simpa [sceneQNorm, sceneLinkData, AdelicThetaLinkData.ofTateParameters,
    sceneTateData, TateParameterData.qOrder] using h

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
    sceneInput 5 2 (Fin 1) inferInstance (fun _ => sceneQTerm)
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
    (sceneTateData.norm rationalTwoPlace) ^ (1 / 10 : ℝ)
  change (sceneLinkData.qNorm rationalTwoPlace) ^
      (1 / (2 * (sceneTarget.ell : ℝ))) =
    (sceneTateData.norm rationalTwoPlace) ^ (1 / 10 : ℝ)
  congr 1 <;> norm_num [sceneTarget, sceneLinkData, sceneTateData]

noncomputable def sceneSourcePair :
    @Corollary312SourceQPair ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  exact
    { rationalPrime := Arithmetic.residueChar sceneSourcePlace.1
      rationalPrime_prime := Arithmetic.residueChar_prime sceneSourcePlace.1
      place := sceneSourcePlace
      rationalPrime_eq_residueChar := rfl
      rationalPrime_liesOver := Arithmetic.residueChar_liesOver sceneSourcePlace.1
      tate_place := by
        change rationalTwoPlace ∈ sceneTateData.places
        simp [sceneTateData]
      q_order_coprime := by
        change Nat.Coprime 5 4
        norm_num }

noncomputable def scene_iut_qPilot_source :
    @IutQPilotSource ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  exact
    { badFinset := sceneTarget.scene1.data.link.places
      badFinset_spec := rfl }

noncomputable def scene_qPilot :
    @Corollary312QPilotData ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  exact scene_iut_qPilot_source.toSceneQPilot 2 sceneLink_tate_compatibility

/-! The source normalization now uses the arithmetic q-pilot itself.  The
explicit rational-place facts above provide the local numerical bridge; no
weight is defined by solving the normalization equation. -/
theorem scene_qPilot_source_normalization :
    @Corollary312QPilotSourceNormalization ℚ inferInstance inferInstance ℤ_[2]
      inferInstance 2 inferInstance scene_padicTwo_not_unit
      scene_padicTwo_is_adic_complete sceneTarget
      scene_tate_order_compatibility scene_qPilot := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  refine { uniformizer_log_eq_weighted_residueChar_log := ?_ }
  intro w hw
  have hwLink : w ∈ sceneLinkData.places := by
    rw [← sceneTarget_link_eq]
    exact Corollary312QPilotData.mem_bad 2 scene_qPilot hw
  have hwEq : w = rationalTwoPlace := by
    simpa [sceneLinkData, AdelicThetaLinkData.ofTateParameters, sceneTateData]
      using hwLink
  subst w
  change -Real.log (rationalTwoPlace (2 : ℚ)) =
    Arithmetic.qPilotWeight rationalTwoPlace *
      Real.log (Arithmetic.residueChar rationalTwoPlace)
  rw [rationalTwoPlace_two, rationalTwoPlace_residueChar]
  unfold Arithmetic.qPilotWeight
  rw [rationalTwoPlace_inertDeg]
  norm_num [Arithmetic.qPilotWeight]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

noncomputable def scene_qFamily :
    @Corollary312TateQFamily ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
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
  let groupingEquiv : sceneTarget.qIndex ≃ Fin 1 :=
    { toFun := fun _ => 0
      invFun := fun _ => qZero
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  let grouping : Corollary312SourceQGrouping 2 sceneTarget :=
    { pair := Fin 1
      pairFintype := inferInstance
      pairData := fun _ => sceneSourcePair
      indexEquiv := groupingEquiv }
  exact
    { compatibility := sceneLink_tate_compatibility
      grouping := grouping
      indexEquiv := iEquiv
      grouping_place_eq := by
        intro i
        fin_cases i
        change sceneSourcePlace = sceneSourcePlace
        rfl
      qFactor_eq := by
        intro i
        fin_cases i
        change sceneQFactor =
          Corollary312SourceQFactor 2 sceneTarget sceneSourcePlace
        exact scene_qFactor_source.symm
      qLogTerm_eq := by
        intro i
        fin_cases i
        change sceneQTerm =
          -Real.log (Corollary312SourceQFactor 2 sceneTarget sceneSourcePlace)
        rw [scene_qFactor_source]
        rfl }

noncomputable def scene_qPilot_source_index_bridge :
    @Corollary312QPilotSourceIndexBridge ℚ inferInstance inferInstance ℤ_[2]
      inferInstance 2 inferInstance scene_padicTwo_not_unit
      scene_padicTwo_is_adic_complete sceneTarget sceneVolume scene_qPilot
      scene_qFamily := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  exact Corollary312QPilotSourceIndexBridge.ofGrouping 2 sceneTarget
    sceneVolume scene_qPilot scene_qFamily

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
    @Corollary312TateQAccounting ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget
      sceneVolume scene_qFamily := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  letI := sceneTarget.qIndexFintype
  letI := scene_qFamily.grouping.pairFintype
  letI := sceneTarget.scene1.data.link.packetHull.packetFintype
  letI := sceneTarget.scene1.data.link.packetHull.hullFintype
  let qZero : sceneTarget.qIndex := by
    change Fin 1
    exact 0
  let pairZero : scene_qFamily.grouping.pair :=
    scene_qFamily.grouping.indexEquiv qZero
  have hqZero : qZero = (by
      change Fin 1
      exact 0) := by
    rfl
  have hIndex : scene_qFamily.indexEquiv qZero = sceneSourcePlace := by
    rfl
  have hGrouped :
      Corollary312GroupedSourceQFactor 2 sceneTarget scene_qFamily.grouping pairZero =
        Corollary312SourceQFactor 2 sceneTarget sceneSourcePlace := by
    unfold Corollary312GroupedSourceQFactor Corollary312SourceQFactor
    rw [show pairZero = scene_qFamily.grouping.indexEquiv qZero by rfl]
    rw [scene_qFamily.grouping_place_eq qZero, hIndex]
  let f : sceneTarget.scene1.data.link.packetHull.packet → scene_qFamily.grouping.pair :=
    fun _ => pairZero
  let g : sceneTarget.scene1.data.link.packetHull.hull → scene_qFamily.grouping.pair :=
    fun _ => pairZero
  exact
    { packet_pair := f
      hull_pair := g
      packet_weight_le_source_qLogTerm := by
        intro x
        change sceneQTerm ≤
          -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
            scene_qFamily.grouping pairZero)
        rw [hGrouped]
        rw [← hIndex]
        rw [← scene_qFamily.qLogTerm_eq qZero]
        rfl
      hull_weight_le_source_qLogTerm := by
        intro x
        change sceneQTerm ≤
          -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
            scene_qFamily.grouping pairZero)
        rw [hGrouped]
        rw [← hIndex]
        rw [← scene_qFamily.qLogTerm_eq qZero]
        rfl
      q_accounting := by
        unfold Corollary312PacketSourceQLogSum Corollary312HullSourceQLogSum
          Corollary312SourceQLogSum
        have hGroupSum :
            (∑ a : scene_qFamily.grouping.pair,
                -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
                  scene_qFamily.grouping a)) =
              -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
                scene_qFamily.grouping pairZero) := by
          calc
            (∑ a : scene_qFamily.grouping.pair,
                -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
                  scene_qFamily.grouping a)) =
                ∑ i : sceneTarget.qIndex,
                  -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
                    scene_qFamily.grouping (scene_qFamily.grouping.indexEquiv i)) :=
              (scene_qFamily.grouping.indexEquiv.sum_comp _).symm
            _ = -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
                scene_qFamily.grouping
                  (scene_qFamily.grouping.indexEquiv qZero)) := by
              change
                (∑ _ : Fin 1,
                    -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
                      scene_qFamily.grouping (scene_qFamily.grouping.indexEquiv _))) = _
              simp [hqZero, id]
            _ = -Real.log (Corollary312GroupedSourceQFactor 2 sceneTarget
                scene_qFamily.grouping pairZero) := by
              rfl
        rw [hGroupSum, hGrouped]
        simp [f, g]
        have hPacketCard :
            Fintype.card sceneTarget.scene1.data.link.packetHull.packet = 1 := by
          change Fintype.card (Fin 1) = 1
          simp
        have hHullCard :
            Fintype.card sceneTarget.scene1.data.link.packetHull.hull = 1 := by
          change Fintype.card (Fin 1) = 1
          simp
        rw [hPacketCard, hHullCard]
        norm_num [sceneTarget]
        rw [hGrouped]
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
      ell_prime := by exact Nat.prime_five
      ell_ge_five := by norm_num [sceneTarget]
      ellStar_eq_half_sub_one := by norm_num [sceneTarget]
      ellStar_pos := by norm_num [sceneTarget] }

noncomputable def scene_qPilotData :
    @Corollary312Scene1QPilotData ℚ inferInstance inferInstance ℤ_[2]
      inferInstance 2 inferInstance scene_padicTwo_not_unit
      scene_padicTwo_is_adic_complete :=
  by
    letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
    letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
      scene_padicTwo_is_adic_complete
    exact
      { base := sceneData
        source := scene_iut_qPilot_source
        orderCompatibility := scene_tate_order_compatibility
        sourceNormalization := scene_qPilot_source_normalization
        sourceIndexBridge := scene_qPilot_source_index_bridge }

theorem scene_qPilot_explicit_audit_corollary312 :
    @Corollary312 ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  simpa [scene_qPilotData, sceneData] using
    (JoshiTeich.Act1Scene1.cor312_of_scene1_qPilot_data 2 scene_qPilotData)

theorem scene_explicit_audit_corollary312 :
    @Corollary312 ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance scene_padicTwo_not_unit scene_padicTwo_is_adic_complete sceneTarget := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := scene_padicTwo_not_unit
  letI : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
    scene_padicTwo_is_adic_complete
  simpa [sceneData] using
    (JoshiTeich.Act1Scene1.cor312_of_scene1_data 2 sceneData)

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
