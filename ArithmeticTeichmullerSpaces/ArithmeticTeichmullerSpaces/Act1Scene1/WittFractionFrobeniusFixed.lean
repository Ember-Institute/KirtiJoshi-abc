import ArithmeticTeichmullerSpaces.Act1Scene1.WittFractionFrobeniusRigidity
import Mathlib.FieldTheory.Finite.Basic

/-!
source-id: JT-SCENE1-WITT-FRACTION-FROBENIUS-FIXED
source: Joshi II `se:ff-rings` and `eq:tate-module-of-lubin-tate`,
the constant field needed to compare actual twisted period solutions;
Mathlib finite prime subfields and Witt discrete valuation rings.
fidelity: constructs prime-field Witt coefficients for every integral
Frobenius-fixed vector. For every fixed Witt fraction, constructs a
p-power denominator and a prime-field Witt numerator. A denominator
presentation is a conclusion, not an input. Original proofs; no
reference implementation copied.
boundary: Scene1/Derived; this is an algebraic fraction-field theorem.
Identification with the actual Q_p embedding is a separate consumer;
no completed fixed-field or full Tate-kernel classification is assumed.
-/

namespace JoshiTeich.Act1Scene1.WittFractionFrobeniusFixed

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [Field F] [CharP F p] [PerfectRing F p]

theorem exists_prime_witt_of_frobenius_eq_self (a : WittVector p F)
    (ha : WittVector.frobenius a = a) :
    ∃ b : WittVector p (ZMod p),
      WittVector.map (ZMod.castHom (dvd_refl p) F) b = a := by
  have hc (n : ℕ) : ∃ z : ZMod p, ZMod.castHom (dvd_refl p) F z = a.coeff n := by
    apply RingHom.mem_fieldRange.mp
    rw [ZMod.fieldRange_castHom_eq_bot p]
    apply (Subfield.mem_bot_iff_pow_eq_self F p).mpr
    have h := congrArg (fun v : WittVector p F => v.coeff n) ha
    simpa only [WittVector.coeff_frobenius_charP] using h
  choose c hc using hc
  refine ⟨WittVector.mk p c, ?_⟩
  apply WittVector.ext
  intro n
  simpa only [WittVector.map_coeff, WittVector.coeff_mk] using hc n

private theorem exists_prime_presentation (x : FractionRing (WittVector p F)) :
    ∃ m : ℕ, ∃ y : WittVector p F,
      x * (p : FractionRing (WittVector p F)) ^ m = algebraMap _ _ y := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (WittVector p F) x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' b hb0
  have hfb : algebraMap (WittVector p F) (FractionRing (WittVector p F)) b ≠ 0 := by
    exact fun h => hb0 (IsFractionRing.injective (WittVector p F)
      (FractionRing (WittVector p F)) (h.trans (map_zero _).symm))
  refine ⟨m, a * (u⁻¹ : (WittVector p F)ˣ), ?_⟩
  apply mul_right_cancel₀ ((u.isUnit.map
    (algebraMap (WittVector p F) (FractionRing (WittVector p F)))).ne_zero)
  calc
    _ = x * algebraMap (WittVector p F) (FractionRing (WittVector p F)) b := by
      rw [hu, map_mul, map_pow, map_natCast, mul_assoc]
    _ = algebraMap (WittVector p F) (FractionRing (WittVector p F)) a :=
      (eq_div_iff hfb).mp hx.symm
    _ = _ := by
      rw [← map_mul]
      simp only [mul_assoc, Units.inv_mul, mul_one]

theorem exists_fixed_prime_presentation (x : FractionRing (WittVector p F))
    (hx : WittFractionFrobeniusRigidity.phi p x = x) :
    ∃ m : ℕ, ∃ b : WittVector p (ZMod p),
      x * (p : FractionRing (WittVector p F)) ^ m =
        algebraMap (WittVector p F) (FractionRing (WittVector p F))
          (WittVector.map (ZMod.castHom (dvd_refl p) F) b) := by
  obtain ⟨m, y, hy⟩ := exists_prime_presentation p x
  have hf : WittVector.frobenius y = y := by
    have h := congrArg (WittFractionFrobeniusRigidity.phi p) hy
    rw [map_mul, map_pow, map_natCast, hx,
      WittFractionFrobeniusRigidity.phi_algebraMap] at h
    exact IsFractionRing.injective (WittVector p F) (FractionRing (WittVector p F))
      (h.symm.trans hy)
  obtain ⟨b, hb⟩ := exists_prime_witt_of_frobenius_eq_self p y hf
  exact ⟨m, b, by rw [hb]; exact hy⟩

end
end JoshiTeich.Act1Scene1.WittFractionFrobeniusFixed
