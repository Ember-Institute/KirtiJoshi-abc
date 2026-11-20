import Solutions.Source_ReferenceIutCor312GlobalVolume
import Solutions.Source_ReferenceIutCor312PrincipalVolumeBound
import Solutions.Source_TripodP7
import Solutions.Source_TripodRationalLegendreFiveQPilot
import Solutions.Source_TripodRationalLegendreFiveCompactLocus
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison
import Solutions.Source_ReferenceIutChebyshevExplicit
import Theorems.Thm_AbcAdaptation_Reference_Iut_LocalHeightData_exists_prime_selection
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_le_half_of_pos
import Theorems.Thm_AbcAdaptation_Tripod_cyclicBoundOdd
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

private theorem logQ_le_of_corollary312Variant {D : InitialThetaData AG TG}
    (TL : ThetaLocalData D (LocalConstruct.concreteLocalTheory (K := D.Kt)))
    (QI : QPilotInputs D) (h7 : 7 ≤ D.ℓ)
    (h : Corollary312Variant
      (concreteVariantData D (LocalConstruct.concreteLocalTheory (K := D.Kt)) TL QI)) :
    QI.qPilot.logQ ≤ (126 / 11) * Real.log Real.pi := by
  let n : ℝ := (((D.ℓ - 1) / 2 : ℕ) : ℝ)
  have hnNat : 3 ≤ (D.ℓ - 1) / 2 := by omega
  have hℓNat : D.ℓ = 2 * ((D.ℓ - 1) / 2) + 1 := by
    have hprime : D.ℓ.Prime := D.prime.ℓ_prime
    obtain ⟨k, hk⟩ := hprime.odd_of_ne_two (by omega)
    omega
  have hn : 3 ≤ n := by
    dsimp only [n]
    exact_mod_cast hnNat
  have hℓ : (D.ℓ : ℝ) = 2 * n + 1 := by
    dsimp only [n]
    exact_mod_cast hℓNat
  have hℓpos : (0 : ℝ) < D.ℓ := by exact_mod_cast D.prime.ℓ_prime.pos
  have hvol := (ThetaLocalData.corollary312Variant_iff_absLogQ_bound TL QI).mp h
  change (((n + 1) * (2 * n + 1) / 6) - 1) * (QI.qPilot.logQ / (2 * (D.ℓ : ℝ))) ≤
    ((n + 3) / 2) * Real.log Real.pi at hvol
  have hcleared :
      (((n + 1) * (2 * n + 1) / 6) - 1) * QI.qPilot.logQ ≤
        ((n + 3) / 2) * Real.log Real.pi * (2 * (D.ℓ : ℝ)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hℓpos)).mp
    rw [mul_div_assoc]
    exact hvol
  apply ThetaLocalData.logQ_le_of_globalVolume_bound hn
  calc
    (n - 1) * (2 * n + 5) * QI.qPilot.logQ =
        6 * ((((n + 1) * (2 * n + 1) / 6) - 1) * QI.qPilot.logQ) := by ring
    _ ≤ 6 * (((n + 3) / 2) * Real.log Real.pi * (2 * (D.ℓ : ℝ))) :=
      mul_le_mul_of_nonneg_left hcleared (by norm_num)
    _ = _ := by rw [hℓ]; ring

/-- At an admissible point of this rational family, the source (P7) principal-region
volume is strictly smaller than its signed q-pilot. -/
theorem exists_sourceP7Counterexample_rationalLegendreFivePoint
    (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG)
    (anab : AnabelianExistence AG TG) (m : ℕ) (hm : 6 ≤ m) :
    let CI := curveInputs_from_source P K d CF hcore northcottHyp
      (legendreHeight P K) (twoAdicBound P K)
    let x := rationalLegendreFivePoint m
    let I := CI.toCorollary22Inputs
    ∀ (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d)
      (_hxe : x ∉ I.excCore) (ℓ : ℕ) (_hℓ : ℓ.Prime) (_h7 : 7 ≤ ℓ)
      (_hP2 : ∀ w ∈ (I.localData x hx).bad, ¬ ℓ ∣ (I.localData x hx).hv w)
      (_hP3 : ∀ w ∈ (I.localData x hx).bad, (I.localData x hx).p w = ℓ →
        ((I.localData x hx).hv w : ℝ) < Real.sqrt (I.h x))
      (_hP6 : I.SL2Image x ℓ),
      ∃ X : Corollary312VariantData.{0, 0} AG TG,
        IsSourceP7Variant CI anab X ∧ X.rhsData.rhs < X.qPilot.lhs := by
  classical
  intro CI x I hx hxe ℓ hℓ h7 hP2 hP3 hP6
  have hmpos : 0 < m := by omega
  have hP5 : ∃ w ∈ (I.localData x hx).bad,
      (I.localData x hx).p w ≠ 2 ∧ (I.localData x hx).p w ≠ ℓ := by
    obtain ⟨w, hw, hchar⟩ := rationalLegendreFivePoint_p5 P m hmpos h7
    exact ⟨w, (P.arith x).badAll_finite.mem_toFinset.mpr hw, hchar⟩
  have hP2' : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw := by
    intro w hw
    have h := hP2 w ((P.arith x).badAll_finite.mem_toFinset.mpr hw)
    change ¬ ℓ ∣ (if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0) at h
    rwa [dif_pos hw] at h
  have hcore' : OrbicurveDataSection.HasCoreUniversally AG (P.curve x).F (P.curve x).E := by
    by_contra h
    exact hxe ⟨hx, h⟩
  let W := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hP6
  have htwo : TwoTorsionRational W.data :=
    two_torsion_curveOf x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)
  let TL := (W.localThetaData htwo).withBadChars W.qPilotInputs
  let X := concreteVariantData W.data W.localTheory TL W.qPilotInputs
  refine ⟨X, ⟨x, hx, hxe, ℓ, hℓ, h7, hP2, hP3, hP5, hP6, htwo, rfl⟩, ?_⟩
  have hq : W.qPilotInputs.qPilot.lhs ≤ -((m : ℝ) * Real.log 5 / (ℓ : ℝ)) :=
    (rationalLegendreFivePoint_qPilot P m hmpos hℓ h7 (hP6 hx hℓ) hP2' anab hcore').2.2
  change -(W.qPilotInputs.qPilot.logQ / (2 * (ℓ : ℝ))) ≤
    -((m : ℝ) * Real.log 5 / (ℓ : ℝ)) at hq
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  have hmul := (div_le_div_iff₀ hℓpos (mul_pos (by norm_num : (0 : ℝ) < 2) hℓpos)).mp
    (neg_le_neg_iff.mp hq)
  have hfive : 2 * (m : ℝ) * Real.log 5 ≤ W.qPilotInputs.qPilot.logQ := by
    apply le_of_mul_le_mul_right _ hℓpos
    nlinarith only [hmul]
  have hlog : Real.log Real.pi < Real.log 5 :=
    Real.log_lt_log Real.pi_pos (Real.pi_lt_four.trans (by norm_num))
  have hmreal : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hlarge : (126 / 11) * Real.log Real.pi < 2 * (m : ℝ) * Real.log 5 :=
    (mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 126 / 11)).trans_le
      (mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by norm_num)))
  apply lt_of_not_ge
  intro h312
  exact (not_le.mpr (hlarge.trans_le hfive))
    (logQ_le_of_corollary312Variant TL W.qPilotInputs (W.prime_eq.symm ▸ h7) h312)

private theorem rationalLegendreFivePoint_injective :
    Function.Injective rationalLegendreFivePoint := by
  intro m n h
  have hparam : rationalLegendreFiveParam m = rationalLegendreFiveParam n := by
    apply (algebraMap ℚ Qbar).injective
    exact congrArg (fun x : Pt => x.1) h
  unfold rationalLegendreFiveParam at hparam
  have hmul := (div_eq_div_iff
    (by positivity : (2 * 5 ^ m + 1 : ℚ) ≠ 0)
    (by positivity : (2 * 5 ^ n + 1 : ℚ) ≠ 0)).mp hparam
  have hpow : (5 : ℚ) ^ m = (5 : ℚ) ^ n := by nlinarith only [hmul]
  exact (pow_right_strictMono₀ (by norm_num : (1 : ℚ) < 5)).injective hpow

/-- Core finiteness, Northcott finiteness, and prime selection supply an admissible
point and prime when the degree-one family lies in the chosen compactly bounded locus. -/
theorem exists_sourceP7Counterexample_rationalLegendreFive
    (P : CurveProviders) (K : CompactlyBounded) {TK : ℝ}
    (CF : CurveFactsProp P K 1 TK) (hcore : CoreFinitenessHyp P K 1 AG)
    (anab : AnabelianExistence AG TG) (hK : ∀ m, rationalLegendreFivePoint m ∈ K.set) :
    let CI := curveInputs_from_source P K 1 CF hcore northcottHyp
      (legendreHeight P K) (twoAdicBound P K)
    ∃ X : Corollary312VariantData.{0, 0} AG TG,
      IsSourceP7Variant CI anab X ∧ X.rhsData.rhs < X.qPilot.lhs := by
  classical
  intro CI
  let I := CI.toCorollary22Inputs
  let H := max (chebyshevBoundExplicit.ξ ^ 2) (49 + 8 * max I.TK 0 + I.B)
  let E := (I.excCore ∩ (tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod 1)) ∪
    {x | x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod 1 ∧ I.h x ≤ H}
  have hE : E.Finite := I.excCore_finite.union (I.northcott H)
  obtain ⟨N, hN⟩ := (hE.preimage rationalLegendreFivePoint_injective.injOn).bddAbove
  let m := max 6 (N + 1)
  let x := rationalLegendreFivePoint m
  have hm : 6 ≤ m := le_max_left _ _
  have hmN : N < m := (Nat.lt_succ_self N).trans_le (le_max_right _ _)
  have havoid : x ∉ E := fun hmem => (not_le.mpr hmN) (hN hmem)
  have hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod 1 :=
    ⟨hK m, mem_ptLE.mpr (rationalLegendreFivePoint_deg m).le⟩
  have hxe : x ∉ I.excCore := fun he => havoid (Or.inl ⟨he, hx⟩)
  have hhigh : H < I.h x := lt_of_not_ge fun hh => havoid (Or.inr ⟨hx, hh⟩)
  let L := I.localData x hx
  have hL : L.height = I.h x := I.localData_height x hx
  have hT : 49 + 8 * max I.TK 0 + I.B ≤ I.h x := (le_max_right _ _).trans hhigh.le
  have hlarge : (49 : ℝ) ≤ I.h x := by
    linarith [hT, le_max_right I.TK 0, I.B_nonneg]
  have hξ : chebyshevBoundExplicit.ξ ≤ Real.sqrt L.height := by
    rw [hL]
    exact Real.le_sqrt_of_sq_le ((le_max_left _ _).trans hhigh.le)
  have hδ : (2 : ℝ) ≤ deltaBound 1 := by norm_num [deltaBound]
  have hdeg : (L.deg : ℝ) ≤ deltaBound 1 := by
    unfold deltaBound
    exact_mod_cast I.localData_deg_le x hx
  obtain ⟨ℓ, hℓ, hℓlo, -, hP2, hP3⟩ :=
    L.exists_prime_selection chebyshevBoundExplicit (deltaBound 1) hδ hdeg hξ
  rw [hL] at hℓlo hP3
  have hℓ7 : (7 : ℝ) ≤ ℓ := (Real.le_sqrt_of_sq_le (by nlinarith only [hlarge])).trans hℓlo
  have h7 : 7 ≤ ℓ := by exact_mod_cast hℓ7
  have hP4 : ¬ I.HasCyclicSubgroup x ℓ := by
    intro hcyc
    have hb := I.cyclic_bound x hx ℓ hℓ h7 hP2 hcyc
    have hleft : 48 + 8 * max I.TK 0 < I.h x - L.heightEq 2 := by
      linarith [I.heightEq_two_le x hx]
    have hfactor : 0 < ((ℓ : ℝ) - 2) / 24 := by linarith
    have hlog : Real.log (ℓ : ℝ) ≤ (ℓ : ℝ) - 2 := by
      have hℓpos : (0 : ℝ) < ℓ := by linarith
      linarith [log_le_half_of_pos hℓpos]
    have hright : 2 * ((ℓ : ℝ) - 2) + max I.TK 0 ≤
        ((ℓ : ℝ) - 2) / 24 * (48 + 8 * max I.TK 0) := by
      nlinarith only [mul_nonneg (show 0 ≤ (ℓ : ℝ) - 5 by linarith) (le_max_right I.TK 0)]
    change ((ℓ : ℝ) - 2) / 24 * (I.h x - L.heightEq 2) ≤ 2 * Real.log ℓ + I.TK at hb
    linarith only [hb, hlog, hright, mul_lt_mul_of_pos_left hleft hfactor, le_max_left I.TK 0]
  have hP5 : ∃ w ∈ L.bad, L.p w ≠ 2 ∧ L.p w ≠ ℓ := by
    obtain ⟨w, hw, hchar⟩ := rationalLegendreFivePoint_p5 P m (by omega) h7
    exact ⟨w, (P.arith x).badAll_finite.mem_toFinset.mpr hw, hchar⟩
  have hP6 : I.SL2Image x ℓ := I.sl2_of x hx ℓ hℓ (by omega) hP2 hP4 hP5
  exact exists_sourceP7Counterexample_rationalLegendreFivePoint P K 1 CF hcore anab m hm
    hx hxe ℓ hℓ h7 hP2 hP3 hP6

/-- For the fixed degree-one locus of this family, the source construction gives
a principal-region counterexample under the provider and geometry inputs. -/
theorem exists_sourceP7Counterexample_rationalLegendreFiveLocus
    (P : CurveProviders) (hcore : CoreFinitenessHyp P rationalLegendreFiveLocus 1 AG)
    (anab : AnabelianExistence AG TG) :
    let K := rationalLegendreFiveLocus
    let CF : CurveFactsProp P K 1
        (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K 1⟩
    let CI := curveInputs_from_source P K 1 CF hcore northcottHyp
      (legendreHeight P K) (twoAdicBound P K)
    ∃ X : Corollary312VariantData.{0, 0} AG TG,
      IsSourceP7Variant CI anab X ∧ X.rhsData.rhs < X.qPilot.lhs := by
  intro K CF CI
  exact exists_sourceP7Counterexample_rationalLegendreFive P K CF hcore anab
    rationalLegendreFivePoint_mem_locus

end AbcAdaptation.Tripod
