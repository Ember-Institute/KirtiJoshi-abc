import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRationalCohomology

/-!
source-id: JT-SCENE1-TATE-FINITE-LEVEL-COORDINATE-BOUND
source: original primitive Tate basis, reduction modulo p^n and the actual
p-adic coefficient norm. No topology or scalar action is transported.
fidelity: equality at level n bounds the difference of rational Tate
coordinates by |p|^n. This is uniform in the Tate elements.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Rational
universe v
noncomputable section
variable (p : ℕ) [Fact p.Prime] {Ω : Type v} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]

theorem coordinate_reduction_eq_zero_of_level_one (t : cyclotomicTateGroup p Ω) (n : ℕ)
    (ht : t.1 n = 1) :
    PadicInt.toZModPow n ((TateBasis.equiv (p := p) (Ω := Ω)).symm (Additive.ofMul t)) = 0 := by
  let z := (TateBasis.equiv (p := p) (Ω := Ω)).symm (Additive.ofMul t)
  letI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have htz : padicPower z (TateBasis.generator (p := p) (Ω := Ω)) = t :=
    congrArg Additive.toMul ((TateBasis.equiv (p := p) (Ω := Ω)).apply_symm_apply (Additive.ofMul t))
  have hlevel := congrArg (fun x : cyclotomicTateGroup p Ω => x.1 n) htz
  rw [padicPower_apply, ht] at hlevel
  have hm := (TateBasis.generator_isPrimitive (p := p) (Ω := Ω) n).pow_inj
    (ZMod.val_lt (PadicInt.toZModPow n z)) (pow_pos (Fact.out : p.Prime).pos n)
    (by simpa only [pow_zero] using hlevel)
  apply ZMod.val_injective
  simpa only [ZMod.val_zero] using hm

theorem norm_coefficientMap_le_prime_pow_of_level_one
    (t : cyclotomicTateGroup p Ω) (n : ℕ) (ht : t.1 n = 1) :
    ‖coefficientMap p (Additive.ofMul t)‖ ≤ ‖(p : ℚ_[p])‖ ^ n := by
  let z := (TateBasis.equiv (p := p) (Ω := Ω)).symm (Additive.ofMul t)
  have hz : z ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    exact coordinate_reduction_eq_zero_of_level_one p t n ht
  have hn := (PadicInt.norm_le_pow_iff_mem_span_pow z n).mpr hz
  change ‖z‖ ≤ _
  simpa only [Padic.norm_p, zpow_neg, zpow_natCast, inv_pow] using hn

theorem norm_coefficientMap_sub_le_prime_pow_of_level_eq
    (s t : cyclotomicTateGroup p Ω) (n : ℕ) (hst : s.1 n = t.1 n) :
    ‖coefficientMap p (Additive.ofMul s) - coefficientMap p (Additive.ofMul t)‖ ≤
      ‖(p : ℚ_[p])‖ ^ n := by
  rw [← map_sub]
  exact norm_coefficientMap_le_prime_pow_of_level_one p (s / t) n
    (by change s.1 n / t.1 n = 1; rw [hst, div_self'])

end
end JoshiTeich.Act1Scene1.LocalKummer.Rational
