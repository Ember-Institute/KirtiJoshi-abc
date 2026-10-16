import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerIntegralLogLattice
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
source-id: JT-SCENE1-INTEGRAL-KUMMER-LOG-TOPOLOGY
source: the original principal logarithm image, small-ball logarithm
surjectivity and the integral-image intersection; Joshi III 3227--3236.
fidelity: the unscaled log image is an open Z_p submodule with full Q_p
span. Its inverse in the original saturated H1 space is exactly the set
of classes admitting integral coefficient lifts, with its original topology.
boundary: Scene1/Derived; no H1e/BK identification is asserted.
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued Topology
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)
variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]
local instance integralLogScalar : Module ℤ_[p] k :=
  Module.compHom k (algebraMap ℤ_[p] ℚ_[p])

def integralLogSubmodule : Submodule ℤ_[p] k where
  toAddSubmonoid := (principalLogImage p hpk).toAddSubmonoid
  smul_mem' := by
    rintro r z ⟨a, rfl⟩
    refine ⟨Additive.ofMul (principalPadicPower hpk a.toMul r), ?_⟩
    exact padicLog_principalPadicPower hpk a.toMul r

theorem smallBall_subset_integralLogSubmodule :
    Metric.closedBall (0 : k) ‖2 * (p : k)‖ ⊆ integralLogSubmodule p hpk := by
  intro z hz
  have hz' : ‖z‖ ≤ ‖2 * (p : k)‖ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  obtain ⟨a, ha, hlog⟩ := exists_padicLog_eq (Fact.out : p.Prime) hpk hz'
  apply (mem_principalLogImage_iff p hpk z).mpr
  exact ⟨1 + a, by simpa only [add_sub_cancel_left] using ha.trans_lt (norm_two_mul_lt_one hpk), hlog.symm⟩

theorem integralLogSubmodule_isOpen : IsOpen (integralLogSubmodule (k := k) p hpk : Set k) := by
  apply AddSubgroup.isOpen_of_mem_nhds (integralLogSubmodule p hpk).toAddSubgroup
  have hr : 0 < ‖2 * (p : k)‖ := norm_pos_iff.mpr
    (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  exact Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : k) hr)
    (smallBall_subset_integralLogSubmodule p hpk)

theorem integralLogSubmodule_span_eq_top :
    Submodule.span ℚ_[p] (integralLogSubmodule (k := k) p hpk : Set k) = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨n, a, ha⟩ := exists_prime_power_mul_eq_principalLog p hpk z
  have hm : padicLog (a.1 : k) ∈ integralLogSubmodule p hpk := ⟨Additive.ofMul a, rfl⟩
  have hz : z = ((p : ℚ_[p]) ^ n)⁻¹ • padicLog (a.1 : k) := by
    rw [ha, Algebra.smul_def, map_inv₀, map_pow, map_natCast, inv_mul_cancel_left₀]
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω]
local notation "HI" => continuousCohomology 1 (LocalKummer.padicTateTopRep (K := k) (Ω := Ω) p)
local notation "HQ" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)
local notation "S" => saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk
local instance integralH1Scalar : Module ℤ_[p] S :=
  Module.compHom S (algebraMap ℤ_[p] ℚ_[p])

/-- The actual integral coefficient image inside the original saturated H1 subspace. -/
def integralKummerSubmodule : Submodule ℤ_[p] S where
  carrier := {x | saturatedPadicLog p hpk x ∈ integralLogSubmodule p hpk}
  zero_mem' := by change saturatedPadicLog p hpk 0 ∈ integralLogSubmodule p hpk; rw [map_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro x y hx hy
    change saturatedPadicLog p hpk (x + y) ∈ integralLogSubmodule p hpk
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  smul_mem' := by
    intro r x hx
    change saturatedPadicLog p hpk ((r : ℚ_[p]) • x) ∈ integralLogSubmodule p hpk
    rw [map_smul]
    exact (integralLogSubmodule p hpk).smul_mem r hx

theorem mem_integralKummerSubmodule_iff (x : S) :
    x ∈ integralKummerSubmodule p hpk ↔ ∃ y : HI, LocalKummer.Rational.standardMap p y = (x : HQ) :=
  (integralLift_iff_log_mem_principalLogImage p hpk x).symm

variable [FiniteDimensional ℚ_[p] k]

def integralKummerLogEquiv :
    integralKummerSubmodule (Ω := Ω) p hpk ≃L[ℤ_[p]] integralLogSubmodule (k := k) p hpk where
  toFun x := ⟨saturatedPadicLog p hpk x.1, x.2⟩
  invFun y := ⟨(saturatedPadicLogContinuousEquiv (Ω := Ω) p hpk).symm y.1, by
    change saturatedPadicLog p hpk _ ∈ integralLogSubmodule p hpk
    have he : saturatedPadicLog p hpk
        ((saturatedPadicLogContinuousEquiv (Ω := Ω) p hpk).symm y.1) = y.1 :=
      (saturatedPadicLogContinuousEquiv (Ω := Ω) p hpk).apply_symm_apply y.1
    rw [he]
    exact y.2⟩
  left_inv x := Subtype.ext ((saturatedPadicLogContinuousEquiv p hpk).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((saturatedPadicLogContinuousEquiv p hpk).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add (saturatedPadicLog p hpk) x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul (saturatedPadicLog p hpk) (r : ℚ_[p]) x.1)
  continuous_toFun := continuous_induced_rng.mpr
    ((saturatedPadicLog_continuous (Ω := Ω) p hpk).comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr
    ((saturatedPadicLogContinuousEquiv (Ω := Ω) p hpk).symm.continuous.comp continuous_subtype_val)

theorem integralKummerSubmodule_isOpen : IsOpen (integralKummerSubmodule (Ω := Ω) p hpk : Set S) :=
  (integralLogSubmodule_isOpen p hpk).preimage (saturatedPadicLog_continuous p hpk)

end
end JoshiTeich.Act1Scene1.LocalPadicLog
