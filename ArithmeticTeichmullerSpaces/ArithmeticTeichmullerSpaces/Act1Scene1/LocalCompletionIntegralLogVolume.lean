import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerIntegralLogTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionIntegralShellNormalization
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaarNorm

/-!
source-id: JT-SCENE1-ACTUAL-INTEGRAL-LOG-VOLUME
source: actual compact integer-ring units, continuous full-unit logarithm,
small-ball surjectivity and Haar character; Joshi III 2843--2853, 3227--3236.
fidelity: the original integral log image is compact, open and spans the
actual local completion. The paper shell has positive finite Haar volume;
multiplying it by p* gives the original log image and multiplies volume by
the actual completion norm of p*. No paper thetaVolume/BK identity is used.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open NumberField MeasureTheory
open JoshiTeich.Prologue.Arithmetic
open scoped Valued Pointwise ENNReal
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
local instance logVolumePrime : Fact (residueChar w).Prime := ⟨residueChar_prime w⟩
local instance logVolumeCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local instance logVolumeAlgebra : Algebra ℚ_[residueChar w] (completionAt K w) :=
  padicAlgebra (w := w) rfl
local instance logVolumeContinuousSMul : ContinuousSMul ℚ_[residueChar w] (completionAt K w) :=
  continuousSMul_of_algebraMap _ _ (continuous_padicEmb (w := w) rfl)
local instance logVolumeFinite : FiniteDimensional ℚ_[residueChar w] (completionAt K w) :=
  finite_padicAlgebra (w := w) rfl

private theorem logVolume_norm_prime_lt_one : ‖(residueChar w : completionAt K w)‖ < 1 := by
  have h := norm_natCast_prime_lt_one (p := residueChar w) (w := w) rfl
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

abbrev integralLog := LocalPadicLog.integralLogSubmodule (k := completionAt K w)
  (residueChar w) (logVolume_norm_prime_lt_one w)

theorem integralLog_isCompact : IsCompact (integralLog w : Set (completionAt K w)) := by
  change IsCompact (LocalPadicLog.principalLogImage (k := completionAt K w)
    (residueChar w) (logVolume_norm_prime_lt_one w) : Set (completionAt K w))
  rw [principalLogImage_eq_unitLog_image]
  exact isCompact_range (unitLog_continuous w)

theorem integralLog_isOpen : IsOpen (integralLog w : Set (completionAt K w)) :=
  LocalPadicLog.integralLogSubmodule_isOpen _ _

theorem integralLog_span_eq_top :
    Submodule.span ℚ_[residueChar w] (integralLog w : Set (completionAt K w)) = ⊤ :=
  LocalPadicLog.integralLogSubmodule_span_eq_top _ _

/-- The carrier is the actual integral coefficient image inside saturated H1. -/
abbrev integralKummer := LocalPadicLog.integralKummerSubmodule
  (k := completionAt K w) (Ω := AlgebraicClosure (completionAt K w))
  (residueChar w) (logVolume_norm_prime_lt_one w)

theorem integralKummer_isCompact : IsCompact (integralKummer w : Set
    (LocalPadicLog.saturatedKummerPadicSubmodule (k := completionAt K w)
      (Ω := AlgebraicClosure (completionAt K w)) (residueChar w) (logVolume_norm_prime_lt_one w))) :=
  (LocalPadicLog.saturatedPadicLogContinuousEquiv
    (k := completionAt K w) (Ω := AlgebraicClosure (completionAt K w))
    (residueChar w) (logVolume_norm_prime_lt_one w)).toHomeomorph.isCompact_preimage.mpr
      (integralLog_isCompact w)

theorem integralKummer_isOpen : IsOpen (integralKummer w : Set
    (LocalPadicLog.saturatedKummerPadicSubmodule (k := completionAt K w)
      (Ω := AlgebraicClosure (completionAt K w)) (residueChar w) (logVolume_norm_prime_lt_one w))) :=
  LocalPadicLog.integralKummerSubmodule_isOpen _ _

theorem logShell_isCompact :
    IsCompact (LocalPadicLog.logShell (k := completionAt K w) (residueChar w)) := by
  rw [logShell_eq_scaled_unitLog_image]
  have he : {y : completionAt K w | ∃ a : (integerRing w)ˣ,
      y = (LocalPadicLog.paperScale (residueChar w) : completionAt K w)⁻¹ * unitLog w (Additive.ofMul a)} =
      Set.range (fun a : (integerRing w)ˣ =>
        (LocalPadicLog.paperScale (residueChar w) : completionAt K w)⁻¹ * unitLog w (Additive.ofMul a)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]
  rw [he]
  exact isCompact_range (continuous_const.mul (unitLog_continuous w))

theorem logShell_isOpen :
    IsOpen (LocalPadicLog.logShell (k := completionAt K w) (residueChar w)) := by
  apply AddSubgroup.isOpen_of_mem_nhds
    (LocalPadicLog.logShellIntegralSubmodule (residueChar w) (logVolume_norm_prime_lt_one w)).toAddSubgroup
  exact Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : completionAt K w) zero_lt_one)
    (LocalPadicLog.closedBall_subset_logShell (residueChar_prime w) (logVolume_norm_prime_lt_one w))

theorem integralLog_haar_pos : 0 < normalizedHaar w (integralLog w : Set (completionAt K w)) :=
  (integralLog_isOpen w).measure_pos (normalizedHaar w) ⟨0, (integralLog w).zero_mem⟩

theorem integralLog_haar_ne_top : normalizedHaar w (integralLog w : Set (completionAt K w)) ≠ ∞ :=
  (integralLog_isCompact w).measure_ne_top

theorem logShell_haar_pos :
    0 < normalizedHaar w (LocalPadicLog.logShell (k := completionAt K w) (residueChar w)) :=
  (logShell_isOpen w).measure_pos (normalizedHaar w) ⟨0, by
    exact (LocalPadicLog.logShellIntegralSubmodule _ (logVolume_norm_prime_lt_one w)).zero_mem⟩

theorem logShell_haar_ne_top :
    normalizedHaar w (LocalPadicLog.logShell (k := completionAt K w) (residueChar w)) ≠ ∞ :=
  (logShell_isCompact w).measure_ne_top

/-- The Haar character of a contracting scalar is its original completion norm. -/
theorem distribHaarChar_toReal_eq_norm (c : completionAt K w) (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    ((distribHaarChar (completionAt K w) (Units.mk0 c hc0) : ENNReal)).toReal = ‖c‖ := by
  rw [← normalizedHaar_scalarBall]
  let z : integerRing w := ⟨c, Valued.toNormedField.norm_le_one_iff.mp hc1.le⟩
  exact normalizedHaar_scalarBall_toReal_eq_norm w z
    (fun hz => hc0 (congrArg (fun x : integerRing w => (x : completionAt K w)) hz))
    (completionQOrder w c) (completionQOrder_valued w c hc0 hc1)

theorem integralLog_volume_eq_paperScale_mul_shell :
    (normalizedHaar w (integralLog w : Set (completionAt K w))).toReal =
      ‖(LocalPadicLog.paperScale (residueChar w) : completionAt K w)‖ *
        (normalizedHaar w (LocalPadicLog.logShell (k := completionAt K w) (residueChar w))).toReal := by
  let c : completionAt K w := LocalPadicLog.paperScale (residueChar w)
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (residueChar_prime w))
  have hc1 : ‖c‖ < 1 :=
    (LocalPadicLog.norm_paperScale_eq_norm_two_mul (residueChar_prime w) (logVolume_norm_prime_lt_one w)).trans_lt
      (LocalPadicLog.norm_two_mul_lt_one (logVolume_norm_prime_lt_one w))
  have himage : (Units.mk0 c hc0) • LocalPadicLog.logShell (k := completionAt K w) (residueChar w) =
      (integralLog w : Set (completionAt K w)) :=
    LocalPadicLog.paperScale_mul_logShell_eq_principalLogImage _ (logVolume_norm_prime_lt_one w)
  have h := distribHaarChar_mul (normalizedHaar w) (Units.mk0 c hc0)
    (LocalPadicLog.logShell (k := completionAt K w) (residueChar w))
  rw [himage] at h
  have ht := congrArg ENNReal.toReal h.symm
  rw [ENNReal.toReal_mul, distribHaarChar_toReal_eq_norm w c hc0 hc1] at ht
  exact ht

theorem integralLog_volume_lt_shell :
    (normalizedHaar w (integralLog w : Set (completionAt K w))).toReal <
      (normalizedHaar w (LocalPadicLog.logShell (k := completionAt K w) (residueChar w))).toReal := by
  rw [integralLog_volume_eq_paperScale_mul_shell]
  have hc1 : ‖(LocalPadicLog.paperScale (residueChar w) : completionAt K w)‖ < 1 :=
    (LocalPadicLog.norm_paperScale_eq_norm_two_mul (residueChar_prime w) (logVolume_norm_prime_lt_one w)).trans_lt
      (LocalPadicLog.norm_two_mul_lt_one (logVolume_norm_prime_lt_one w))
  exact mul_lt_of_lt_one_left
    (ENNReal.toReal_pos (logShell_haar_pos w).ne' (logShell_haar_ne_top w)) hc1

theorem shell_logVolume_sub_integralLog_logVolume :
    Real.log (normalizedHaar w (LocalPadicLog.logShell (k := completionAt K w) (residueChar w))).toReal -
      Real.log (normalizedHaar w (integralLog w : Set (completionAt K w))).toReal =
        -Real.log ‖(LocalPadicLog.paperScale (residueChar w) : completionAt K w)‖ := by
  have hc : ‖(LocalPadicLog.paperScale (residueChar w) : completionAt K w)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (residueChar_prime w)))
  have hs : (normalizedHaar w (LocalPadicLog.logShell (k := completionAt K w) (residueChar w))).toReal ≠ 0 :=
    (ENNReal.toReal_pos (logShell_haar_pos w).ne' (logShell_haar_ne_top w)).ne'
  rw [integralLog_volume_eq_paperScale_mul_shell, Real.log_mul hc hs]
  ring

end
end JoshiTeich.Act1Scene1.LocalCompletion
