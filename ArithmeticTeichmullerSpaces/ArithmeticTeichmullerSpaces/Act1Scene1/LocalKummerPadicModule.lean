import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerContinuity
import Mathlib.NumberTheory.Padics.RingHoms

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-PADIC-MODULE
source: Joshi III Z_p(1) coefficients (3190--3208); inverse-limit scalar action.
fidelity: defines a p-adic scalar by its exponent modulo p^n at each level.
It proves compatibility, the module laws, joint continuity and Galois equivariance.
The topology remains the product subspace topology on compatible roots of unity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {p : ℕ} [Fact p.Prime] {Ω : Type v} [Field Ω]

local instance levelModNeZero (n : ℕ) : NeZero (p ^ n) :=
  ⟨(pow_pos (Fact.out : p.Prime).pos n).ne'⟩

theorem toZModPow_isLocallyConstant (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  have heps : 0 < (p : ℝ) ^ (-(n : ℤ)) :=
    zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
  refine ⟨Metric.ball x ((p : ℝ) ^ (-(n : ℤ))), Metric.isOpen_ball,
    Metric.mem_ball_self heps, ?_⟩
  intro y hy
  apply sub_eq_zero.mp
  rw [← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)

def padicPower (r : ℤ_[p]) (x : cyclotomicTateGroup p Ω) : cyclotomicTateGroup p Ω :=
  ⟨fun n => x.1 n ^ (PadicInt.toZModPow n r).val, by
    constructor
    · intro n
      rw [← pow_mul, Nat.mul_comm, pow_mul, x.2.1 n, one_pow]
    · intro n
      rw [← pow_mul, Nat.mul_comm, pow_mul, x.2.2 n]
      have h := congrArg ZMod.val (PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) r)
      simp only [ZMod.cast_eq_val, ZMod.val_natCast] at h
      rw [pow_eq_pow_mod _ (x.2.1 n), h]⟩

theorem padicPower_apply (r : ℤ_[p]) (x : cyclotomicTateGroup p Ω) (n : ℕ) :
    (padicPower r x).1 n = x.1 n ^ (PadicInt.toZModPow n r).val := rfl

theorem padicPower_natCast (m : ℕ) (x : cyclotomicTateGroup p Ω) :
    padicPower (m : ℤ_[p]) x = x ^ m := by
  apply Subtype.ext
  funext n
  change x.1 n ^ (PadicInt.toZModPow n (m : ℤ_[p])).val = x.1 n ^ m
  rw [map_natCast, ZMod.val_natCast]
  exact (pow_eq_pow_mod m (x.2.1 n)).symm

theorem padicPower_add (r s : ℤ_[p]) (x : cyclotomicTateGroup p Ω) :
    padicPower (r + s) x = padicPower r x * padicPower s x := by
  apply Subtype.ext
  funext n
  change x.1 n ^ (PadicInt.toZModPow n (r + s)).val =
    x.1 n ^ (PadicInt.toZModPow n r).val * x.1 n ^ (PadicInt.toZModPow n s).val
  rw [map_add, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (x.2.1 n)]

theorem padicPower_mul (r s : ℤ_[p]) (x : cyclotomicTateGroup p Ω) :
    padicPower (r * s) x = padicPower r (padicPower s x) := by
  apply Subtype.ext
  funext n
  change x.1 n ^ (PadicInt.toZModPow n (r * s)).val =
    (x.1 n ^ (PadicInt.toZModPow n s).val) ^ (PadicInt.toZModPow n r).val
  rw [map_mul, ZMod.val_mul, ← pow_eq_pow_mod _ (x.2.1 n), ← pow_mul, Nat.mul_comm]

theorem padicPower_mul_tate (r : ℤ_[p]) (x y : cyclotomicTateGroup p Ω) :
    padicPower r (x * y) = padicPower r x * padicPower r y := by
  apply Subtype.ext
  funext n
  exact mul_pow (x.1 n) (y.1 n) _

instance tatePadicModule : Module ℤ_[p] (Additive (cyclotomicTateGroup p Ω)) where
  smul r x := Additive.ofMul (padicPower r x.toMul)
  one_smul x := by
    change padicPower (1 : ℤ_[p]) x.toMul = x.toMul
    simpa only [Nat.cast_one, pow_one] using padicPower_natCast 1 x.toMul
  mul_smul r s x := padicPower_mul r s x.toMul
  smul_zero r := by
    change padicPower r (1 : cyclotomicTateGroup p Ω) = 1
    apply Subtype.ext
    funext n
    exact one_pow _
  smul_add r x y := padicPower_mul_tate r x.toMul y.toMul
  add_smul r s x := padicPower_add r s x.toMul
  zero_smul x := by
    change padicPower (0 : ℤ_[p]) x.toMul = 1
    simpa only [Nat.cast_zero, pow_zero] using padicPower_natCast 0 x.toMul

theorem padic_smul_natCast (m : ℕ) (x : Additive (cyclotomicTateGroup p Ω)) :
    (m : ℤ_[p]) • x = m • x :=
  congrArg Additive.ofMul (padicPower_natCast m x.toMul)

theorem continuous_padicPower :
    Continuous (fun z : ℤ_[p] × cyclotomicTateGroup p Ω => padicPower z.1 z.2) := by
  apply (continuous_tate_iff_level_locallyConstant _).mpr
  intro n
  have hr := (toZModPow_isLocallyConstant (p := p) n).comp_continuous
    (continuous_fst : Continuous (fun z : ℤ_[p] × cyclotomicTateGroup p Ω => z.1))
  have hx := (continuous_tate_iff_level_locallyConstant
    (fun z : ℤ_[p] × cyclotomicTateGroup p Ω => z.2)).mp continuous_snd n
  exact hr.comp₂ hx (fun a b => b ^ a.val)

instance tatePadicContinuousSMul : ContinuousSMul ℤ_[p] (Additive (cyclotomicTateGroup p Ω)) where
  continuous_smul :=
    continuous_ofMul.comp (continuous_padicPower.comp
      (show Continuous (fun z : ℤ_[p] × Additive (cyclotomicTateGroup p Ω) =>
        (z.1, z.2.toMul)) from continuous_fst.prodMk (continuous_toMul.comp continuous_snd)))

variable {K : Type u} [Field K] [Algebra K Ω]

theorem tateAction_padicPower (σ : Ω ≃ₐ[K] Ω) (r : ℤ_[p]) (x : cyclotomicTateGroup p Ω) :
    σ • padicPower r x = padicPower r (σ • x) := by
  apply Subtype.ext
  funext n
  exact smul_pow' σ (x.1 n) _

end
end JoshiTeich.Act1Scene1.LocalKummer
