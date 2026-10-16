import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerDividedIntegralLift
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedPadicModule

/-!
source-id: JT-SCENE1-KUMMER-INTEGRAL-INTERSECTION
source: finite-level integral-lift root criterion, actual local principal
units and the original saturated rational Kummer carrier; Joshi III 3227--3236.
fidelity: inside the original saturated subspace, classes admitting an
integral lift are exactly the original principal-unit Kummer image.
This compares actual coefficient images, without naming them H1e/BK.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)
local notation "HI" => continuousCohomology 1 (LocalKummer.padicTateTopRep (K := k) (Ω := Ω) p)
local notation "HQ" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)

include hpk in
theorem integralLift_iff_mem_principalImage (x : saturatedKummerImage (k := k) (Ω := Ω) p) :
    (∃ y : HI, LocalKummer.Rational.standardMap p y = (x : HQ)) ↔
      (x : HQ) ∈ principalKummerImage p := by
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := x.2
    obtain ⟨a, ha⟩ := hm
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hxval : (x : HQ) = ((p : ℚ_[p]) ^ m)⁻¹ •
        (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p a.toMul.1).toAdd := by
      have hmul : (p : ℚ_[p]) ^ m • (x : HQ) =
          (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p a.toMul.1).toAdd := by
        change (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p a.toMul.1).toAdd =
          (p ^ m) • (x : HQ) at ha
        simpa only [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow] using ha.symm
      rw [← hmul, smul_smul, inv_mul_cancel₀ (pow_ne_zero m hp0), one_smul]
    have hlift : ∃ y : HI, LocalKummer.Rational.standardMap p y =
        ((p : ℚ_[p]) ^ m)⁻¹ • (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p a.toMul.1).toAdd := by
      simpa only [hxval] using hx
    obtain ⟨n, b, hb⟩ := (LocalKummer.Rational.exists_integralLift_dividedKummer_iff
      (Ω := Ω) p a.toMul.1 m).mp hlift
    have hbprincipal : ‖b - 1‖ < 1 :=
      norm_sub_one_lt_of_pow_prime_pow (Fact.out : p.Prime) hpk (m + n)
        (by rw [hb]; exact norm_pow_sub_one_lt a.toMul.2 (p ^ n))
    let B : principalUnits (k := k) :=
      ⟨Units.mk0 b (ne_zero_of_norm_sub_one_lt hbprincipal), hbprincipal⟩
    refine ⟨Additive.ofMul B, ?_⟩
    change (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p B.1).toAdd = (x : HQ)
    rw [hxval]
    exact LocalKummer.Rational.kummer_eq_divided_of_power_root p a.toMul.1 B.1 m n (Units.ext hb)
  · rintro ⟨a, ha⟩
    refine ⟨LocalKummer.Rational.integralUnitClass p a.toMul.1, ?_⟩
    rw [LocalKummer.Rational.standardMap_integralUnitClass]
    exact ha

end
end JoshiTeich.Act1Scene1.LocalPadicLog
