import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerFiniteRootDescent
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerImageLogarithm

/-!
source-id: JT-SCENE1-DIVIDED-KUMMER-INTEGRAL-LIFT
source: finite-level Galois root descent and original Kummer classes,
Joshi III 3214--3236.
fidelity: a p-power-divided rational Kummer class has an integral lift iff
a concrete power-root equation has a solution in the base field. Both
directions use the original coefficient map; no Kummer surjectivity is assumed.
boundary: Scene1/Derived; H1e/BK and root existence remain separate.
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Rational
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [IsGalois K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]
local notation "HI" => continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)
local notation "HQ" => continuousCohomology 1 (topRep (K := K) (Ω := Ω) p)

def integralUnitClass (a : Kˣ) : HI :=
  padicClassOfCocycle p ((rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)).continuousCocycleValue
    (Fact.out : p.Prime).pos a.ne_zero)

theorem standardMap_integralUnitClass (a : Kˣ) :
    standardMap p (integralUnitClass (Ω := Ω) p a) =
      (kummerHom (K := K) (Ω := Ω) p a).toAdd :=
  standardMap_classOfCocycle p _

theorem kummerHom_pow_nsmul (a : Kˣ) (m : ℕ) :
    (kummerHom (K := K) (Ω := Ω) p (a ^ m)).toAdd =
      m • (kummerHom (K := K) (Ω := Ω) p a).toAdd :=
  congrArg (fun z : Multiplicative HQ => z.toAdd) (map_pow (kummerHom (K := K) (Ω := Ω) p) a m)

theorem kummer_eq_divided_of_power_root (a B : Kˣ) (m n : ℕ)
    (hpow : B ^ (p ^ (m + n)) = a ^ (p ^ n)) :
    (kummerHom (K := K) (Ω := Ω) p B).toAdd =
      ((p : ℚ_[p]) ^ m)⁻¹ • (kummerHom (K := K) (Ω := Ω) p a).toAdd := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have he := congrArg (fun z : Kˣ => (kummerHom (K := K) (Ω := Ω) p z).toAdd) hpow
  rw [kummerHom_pow_nsmul, kummerHom_pow_nsmul] at he
  have hm : (p : ℚ_[p]) ^ m • (kummerHom (K := K) (Ω := Ω) p B).toAdd = (kummerHom (K := K) (Ω := Ω) p a).toAdd := by
    have hn : (p : ℚ_[p]) ^ n •
        ((p : ℚ_[p]) ^ m • (kummerHom (K := K) (Ω := Ω) p B).toAdd - (kummerHom (K := K) (Ω := Ω) p a).toAdd) = 0 := by
      rw [smul_sub, smul_smul, ← pow_add, Nat.add_comm n m]
      simpa only [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow] using sub_eq_zero.mpr he
    exact sub_eq_zero.mp ((smul_eq_zero.mp hn).resolve_left (pow_ne_zero n hp0))
  rw [← hm, smul_smul, inv_mul_cancel₀ (pow_ne_zero m hp0), one_smul]

theorem exists_integralLift_dividedKummer_iff (a : Kˣ) (m : ℕ) :
    (∃ x : HI, standardMap p x = ((p : ℚ_[p]) ^ m)⁻¹ • (kummerHom (K := K) (Ω := Ω) p a).toAdd) ↔
      ∃ n : ℕ, ∃ b : K, b ^ (p ^ (m + n)) = (a : K) ^ (p ^ n) := by
  have hpI : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨x, hx⟩
    have hdiv : standardMap p x = ((p : ℤ_[p]) ^ m : ℚ_[p])⁻¹ •
        standardMap p (integralUnitClass p a) := by
      simpa only [PadicInt.coe_pow, PadicInt.coe_natCast, standardMap_integralUnitClass] using hx
    obtain ⟨n, hn⟩ := (standardMap_eq_divided_iff p ((p : ℤ_[p]) ^ m)
      (pow_ne_zero m hpI) x (integralUnitClass p a)).mp hdiv
    have he : (p ^ (m + n)) • x = (p ^ n) • integralUnitClass p a := by
      have hz : (p ^ n) • ((p ^ m) • x) - (p ^ n) • integralUnitClass p a = 0 := by
        simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, smul_sub] using hn
      rw [← mul_smul, ← pow_add, Nat.add_comm n m] at hz
      exact sub_eq_zero.mp hz
    exact ⟨n, exists_root_of_class_divisibility p
      (rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)) a.ne_zero m n x he⟩
  · rintro ⟨n, b, hb⟩
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, zero_pow (pow_pos (Fact.out : p.Prime).pos (m + n)).ne'] at hb
      exact pow_ne_zero (p ^ n) a.ne_zero hb.symm
    let B : Kˣ := Units.mk0 b hb0
    have hpow : B ^ (p ^ (m + n)) = a ^ (p ^ n) := Units.ext hb
    refine ⟨integralUnitClass p B, ?_⟩
    rw [standardMap_integralUnitClass]
    exact kummer_eq_divided_of_power_root p a B m n hpow


end
end JoshiTeich.Act1Scene1.LocalKummer.Rational
