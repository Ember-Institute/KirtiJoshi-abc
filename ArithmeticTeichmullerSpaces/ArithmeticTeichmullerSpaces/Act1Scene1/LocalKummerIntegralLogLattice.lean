import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerIntegralIntersection
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerLogShellNormalization

/-!
source-id: JT-SCENE1-INTEGRAL-KUMMER-LOG-LATTICE
source: Joshi III 2843--2853 and 3226--3236, original integral coefficient
image, ordinary principal logarithm and its proved uniform bound.
fidelity: the ordinary log image of integral classes in the saturated
Kummer space is the unscaled principal-log image. The existing p*-scaled
shell strictly contains it. This is a normalization comparison, not an
H1e/BK identification or a claim about the particular normalized witness.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open Filter Topology
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)

/-- The existing ordinary principal logarithm image, with no scale change. -/
def principalLogImage : AddSubgroup k := (principalLogHom (k := k) p hpk).range

theorem mem_principalLogImage_iff (z : k) :
    z ∈ principalLogImage p hpk ↔ ∃ a : k, ‖a - 1‖ < 1 ∧ z = padicLog a := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.toMul.1, a.toMul.2, ha.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Additive.ofMul ⟨Units.mk0 a (ne_zero_of_norm_sub_one_lt ha), ha⟩, rfl⟩

theorem principalLogImage_bounded :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ principalLogImage (k := k) p hpk, ‖z‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_forall_norm_padicLog_le (Fact.out : p.Prime) hpk
  refine ⟨M, hM, ?_⟩
  rintro z ⟨a, rfl⟩
  exact hbound _ a.toMul.2

theorem principalLogImage_ne_bot : principalLogImage (k := k) p hpk ≠ ⊥ := by
  obtain ⟨n, a, ha⟩ := exists_prime_power_mul_eq_principalLog p hpk (1 : k)
  intro hbot
  have hm : padicLog (a.1 : k) ∈ principalLogImage p hpk := ⟨Additive.ofMul a, rfl⟩
  rw [hbot] at hm
  have hz : padicLog (a.1 : k) = 0 := hm
  rw [ha, mul_one] at hz
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hz

variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]

/-- The scale correction identifies the two carriers exactly. -/
theorem paperScale_mul_logShell_eq_principalLogImage :
    (fun z : k => (paperScale p : k) * z) '' logShell p =
      (principalLogImage p hpk : Set k) := by
  have hc : (paperScale p : k) ≠ 0 := Nat.cast_ne_zero.mpr (paperScale_ne_zero (Fact.out : p.Prime))
  rw [logShell_eq_paperPrincipalLogShell p hpk]
  ext z
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    change (paperScale p : k) * ((paperScale p : k)⁻¹ * padicLog a) ∈ principalLogImage p hpk
    rw [mul_inv_cancel_left₀ hc]
    exact (mem_principalLogImage_iff p hpk _).mpr ⟨a, ha, rfl⟩
  · intro hz
    obtain ⟨a, ha, rfl⟩ := (mem_principalLogImage_iff p hpk z).mp hz
    exact ⟨(paperScale p : k)⁻¹ * padicLog a, ⟨a, ha, rfl⟩, mul_inv_cancel_left₀ hc _⟩

theorem principalLogImage_subset_logShell :
    (principalLogImage (k := k) p hpk : Set k) ⊆ logShell p := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := (mem_principalLogImage_iff p hpk z).mp hz
  rw [logShell_eq_paperPrincipalLogShell p hpk]
  refine ⟨a ^ paperScale p, norm_pow_sub_one_lt ha _, ?_⟩
  rw [padicLog_pow (Fact.out : p.Prime) hpk ha, inv_mul_cancel_left₀]
  exact Nat.cast_ne_zero.mpr (paperScale_ne_zero (Fact.out : p.Prime))

theorem logShell_not_subset_principalLogImage :
    ¬ logShell (k := k) p ⊆ (principalLogImage p hpk : Set k) := by
  intro hsub
  let c : k := paperScale p
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.mpr (paperScale_ne_zero (Fact.out : p.Prime))
  have hc1 : ‖c‖ < 1 :=
    (norm_paperScale_eq_norm_two_mul (Fact.out : p.Prime) hpk).trans_lt (norm_two_mul_lt_one hpk)
  have hclosed (z : k) (hz : z ∈ principalLogImage p hpk) :
      c⁻¹ * z ∈ principalLogImage p hpk := by
    apply hsub
    rw [logShell_eq_paperPrincipalLogShell p hpk]
    obtain ⟨a, ha, rfl⟩ := (mem_principalLogImage_iff p hpk z).mp hz
    exact ⟨a, ha, rfl⟩
  obtain ⟨M, hM0, hM⟩ := principalLogImage_bounded (k := k) p hpk
  have hall (z : k) (hz : z ∈ principalLogImage p hpk) : z = 0 := by
    have hmem (n : ℕ) : c⁻¹ ^ n * z ∈ principalLogImage p hpk := by
      induction n with
      | zero => simpa only [pow_zero, one_mul] using hz
      | succ n ih => simpa only [pow_succ', mul_assoc] using hclosed _ ih
    have hbound (n : ℕ) : ‖z‖ ≤ ‖c‖ ^ n * M := by
      calc
        ‖z‖ = ‖c ^ n * (c⁻¹ ^ n * z)‖ := by
          rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc0, one_pow, one_mul]
        _ = ‖c‖ ^ n * ‖c⁻¹ ^ n * z‖ := by rw [norm_mul, norm_pow]
        _ ≤ ‖c‖ ^ n * M := mul_le_mul_of_nonneg_left (hM _ (hmem n)) (pow_nonneg (norm_nonneg _) n)
    have ht : Tendsto (fun n : ℕ => ‖c‖ ^ n * M) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg c) hc1).mul_const M
    exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht (Eventually.of_forall hbound)) (norm_nonneg _))
  apply principalLogImage_ne_bot (k := k) p hpk
  apply le_antisymm _ bot_le
  intro z hz
  exact hall z hz

theorem principalLogImage_ssubset_logShell :
    (principalLogImage (k := k) p hpk : Set k) ⊂ logShell p := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨principalLogImage_subset_logShell p hpk, ?_⟩
  intro he
  apply logShell_not_subset_principalLogImage (k := k) p hpk
  rw [he]

variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω]
local notation "HI" => continuousCohomology 1 (LocalKummer.padicTateTopRep (K := k) (Ω := Ω) p)
local notation "HQ" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)
local notation "S" => saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk

theorem integralLift_iff_log_mem_principalLogImage (x : S) :
    (∃ y : HI, LocalKummer.Rational.standardMap p y = (x : HQ)) ↔
      saturatedPadicLog p hpk x ∈ principalLogImage p hpk := by
  rw [integralLift_iff_mem_principalImage p hpk ⟨x.1, x.2⟩]
  constructor
  · rintro ⟨a, ha⟩
    have hx : x = principalSaturatedClass (Ω := Ω) p hpk a := Subtype.ext ha.symm
    rw [hx, saturatedPadicLog_principalSaturatedClass]
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    have hx : principalSaturatedClass (Ω := Ω) p hpk a = x := by
      apply (saturatedPadicLogEquiv p hpk).injective
      exact (saturatedPadicLog_principalSaturatedClass p hpk a).trans ha
    exact ⟨a, congrArg Subtype.val hx⟩

theorem exists_shell_class_without_integralLift :
    ∃ x : S, x ∈ normalizedKummerShell p hpk ∧
      ¬ ∃ y : HI, LocalKummer.Rational.standardMap p y = (x : HQ) := by
  obtain ⟨z, hz, hnz⟩ := Set.not_subset.mp (logShell_not_subset_principalLogImage (k := k) p hpk)
  let x : S := (saturatedPadicLogEquiv (Ω := Ω) p hpk).symm z
  have hx : saturatedPadicLog p hpk x = z := (saturatedPadicLogEquiv p hpk).apply_symm_apply z
  refine ⟨x, ?_, ?_⟩
  · change saturatedPadicLog p hpk x ∈ logShell p
    rwa [hx]
  · rw [integralLift_iff_log_mem_principalLogImage, hx]
    exact hnz

end
end JoshiTeich.Act1Scene1.LocalPadicLog
