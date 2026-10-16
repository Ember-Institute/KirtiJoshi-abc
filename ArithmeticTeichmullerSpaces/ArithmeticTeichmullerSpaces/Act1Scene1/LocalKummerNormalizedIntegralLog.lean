import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerIntegralLogTopology

/-!
source-id: JT-SCENE1-NORMALIZED-INTEGRAL-KUMMER-LOG
source: original integral coefficient image, ordinary principal logarithm
and the p*-scaled shell; Joshi III 2843--2853, 3226--3236.
fidelity: keeps the original integral image and divides its logarithm by
p*. This gives a continuous Z_p-linear equivalence onto the old shell,
with both original subspace topologies. Scaling the logarithm is distinct
from asserting that a p*-divided rational class has an integral lift.
boundary: Scene1/Derived; no H1e/BK identity is assumed or named.
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)
variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]
local instance normalizedIntegralScalar : Module ℤ_[p] k :=
  Module.compHom k (algebraMap ℤ_[p] ℚ_[p])

theorem mem_integralLog_iff_scale_inv_mem_shell (z : k) :
    z ∈ integralLogSubmodule p hpk ↔ (paperScale p : k)⁻¹ * z ∈ logShell p := by
  have hc : (paperScale p : k) ≠ 0 := Nat.cast_ne_zero.mpr (paperScale_ne_zero (Fact.out : p.Prime))
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := (mem_principalLogImage_iff p hpk z).mp hz
    rw [logShell_eq_paperPrincipalLogShell p hpk]
    exact ⟨a, ha, rfl⟩
  · intro hz
    have hm := Set.mem_image_of_mem (fun y : k => (paperScale p : k) * y) hz
    rw [paperScale_mul_logShell_eq_principalLogImage p hpk, mul_inv_cancel_left₀ hc] at hm
    exact hm

def integralLogToShellEquiv :
    integralLogSubmodule (k := k) p hpk ≃L[ℤ_[p]] logShellIntegralSubmodule p hpk where
  toFun z := ⟨(paperScale p : k)⁻¹ * z.1, (mem_integralLog_iff_scale_inv_mem_shell p hpk z.1).mp z.2⟩
  invFun z := ⟨(paperScale p : k) * z.1, by
    apply (mem_integralLog_iff_scale_inv_mem_shell p hpk _).mpr
    rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (paperScale_ne_zero (Fact.out : p.Prime)))]
    exact z.2⟩
  left_inv z := Subtype.ext (mul_inv_cancel_left₀
    (Nat.cast_ne_zero.mpr (paperScale_ne_zero (Fact.out : p.Prime))) z.1)
  right_inv z := Subtype.ext (inv_mul_cancel_left₀
    (Nat.cast_ne_zero.mpr (paperScale_ne_zero (Fact.out : p.Prime))) z.1)
  map_add' z w := Subtype.ext (mul_add _ _ _)
  map_smul' r z := by
    apply Subtype.ext
    change (paperScale p : k)⁻¹ * ((r : ℚ_[p]) • z.1) =
      (r : ℚ_[p]) • ((paperScale p : k)⁻¹ * z.1)
    simp only [Algebra.smul_def]
    ring
  continuous_toFun := continuous_induced_rng.mpr (continuous_const.mul continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr (continuous_const.mul continuous_subtype_val)

theorem integralLogToShellEquiv_apply (z : integralLogSubmodule (k := k) p hpk) :
    (integralLogToShellEquiv p hpk z : k) = (paperScale p : k)⁻¹ * z.1 := rfl

variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω]
local notation "S" => saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk
local instance normalizedIntegralH1Scalar : Module ℤ_[p] S :=
  Module.compHom S (algebraMap ℤ_[p] ℚ_[p])

def principalIntegralClass (a : Additive (principalUnits (k := k))) :
    integralKummerSubmodule (Ω := Ω) p hpk :=
  ⟨principalSaturatedClass p hpk a, by
    change saturatedPadicLog p hpk (principalSaturatedClass p hpk a) ∈ integralLogSubmodule p hpk
    rw [saturatedPadicLog_principalSaturatedClass]
    exact ⟨a, rfl⟩⟩

variable [FiniteDimensional ℚ_[p] k]

def normalizedIntegralKummerLogEquiv :
    integralKummerSubmodule (Ω := Ω) p hpk ≃L[ℤ_[p]] logShellIntegralSubmodule (k := k) p hpk :=
  (integralKummerLogEquiv p hpk).trans (integralLogToShellEquiv p hpk)

theorem normalizedIntegralKummerLogEquiv_apply (x : integralKummerSubmodule (Ω := Ω) p hpk) :
    (normalizedIntegralKummerLogEquiv p hpk x : k) =
      (paperScale p : k)⁻¹ * saturatedPadicLog p hpk x.1 := rfl

theorem normalizedIntegralKummerLog_principal (a : Additive (principalUnits (k := k))) :
    (normalizedIntegralKummerLogEquiv p hpk (principalIntegralClass (Ω := Ω) p hpk a) : k) =
      (paperScale p : k)⁻¹ * padicLog (a.toMul.1 : k) := by
  rw [normalizedIntegralKummerLogEquiv_apply]
  exact congrArg ((paperScale p : k)⁻¹ * ·) (saturatedPadicLog_principalSaturatedClass p hpk a)

theorem normalizedIntegralKummerLog_eq_dividedClass_log
    (x : integralKummerSubmodule (Ω := Ω) p hpk) :
    (normalizedIntegralKummerLogEquiv p hpk x : k) =
      saturatedPadicLog p hpk ((paperScale p : ℚ_[p])⁻¹ • x.1) := by
  rw [normalizedIntegralKummerLogEquiv_apply, map_smul]
  simp only [Algebra.smul_def, map_inv₀, map_natCast]

end
end JoshiTeich.Act1Scene1.LocalPadicLog
