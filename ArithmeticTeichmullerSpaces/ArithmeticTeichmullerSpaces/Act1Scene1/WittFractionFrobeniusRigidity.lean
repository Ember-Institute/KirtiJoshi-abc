import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusTeichmullerRigidity
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.Localization.FractionRing

/-!
source-id: JT-SCENE1-WITT-FRACTION-FROBENIUS-RIGIDITY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, recognition
of Teichmuller representatives in the bounded Witt localization.
fidelity: for an actual p-power numerator presentation and phi(x)=x^p,
proves phi(y)*p^(m*(p-1))=y^p. If m>0, its zeroth coefficient forces
p to divide y, decreasing the original denominator. Induction removes
every p-denominator and the proved integral rigidity gives a genuine
Teichmuller representative in the original Witt fraction field.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the statement concerns algebraic source
presentations, not arbitrary completed or annular elements.
-/

namespace JoshiTeich.Act1Scene1.WittFractionFrobeniusRigidity

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [Field F] [CharP F p] [PerfectRing F p]

def phi : FractionRing (WittVector p F) ≃+* FractionRing (WittVector p F) :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p F)

theorem phi_algebraMap (a : WittVector p F) :
    phi p (algebraMap (WittVector p F) (FractionRing (WittVector p F)) a) =
      algebraMap (WittVector p F) (FractionRing (WittVector p F)) (WittVector.frobenius a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem numerator_equation (x : FractionRing (WittVector p F)) (hx : phi p x = x ^ p)
    (m : ℕ) (y : WittVector p F)
    (hy : x * (p : FractionRing (WittVector p F)) ^ m = algebraMap _ _ y) :
    WittVector.frobenius y * (p : WittVector p F) ^ (m * (p - 1)) = y ^ p := by
  have hprime := (Fact.out : p.Prime).one_lt
  have hp : 1 + (p - 1) = p := by omega
  have hexp : m + m * (p - 1) = m * p := by
    calc
      _ = m * 1 + m * (p - 1) := by rw [Nat.mul_one]
      _ = m * (1 + (p - 1)) := (Nat.mul_add _ _ _).symm
      _ = _ := by rw [hp]
  have h := congrArg (phi p) hy
  rw [map_mul, map_pow, map_natCast, phi_algebraMap, hx] at h
  apply IsFractionRing.injective (WittVector p F) (FractionRing (WittVector p F))
  simp only [map_mul, map_pow, map_natCast]
  calc
    _ = (x ^ p * (p : FractionRing (WittVector p F)) ^ m) *
        (p : FractionRing (WittVector p F)) ^ (m * (p - 1)) := by rw [h]
    _ = (x * (p : FractionRing (WittVector p F)) ^ m) ^ p := by
      rw [mul_assoc, ← pow_add, hexp, mul_pow, pow_mul]
    _ = _ := by rw [hy]

theorem numerator_prime_dvd (x : FractionRing (WittVector p F)) (hx : phi p x = x ^ p)
    (m : ℕ) (y : WittVector p F)
    (hy : x * (p : FractionRing (WittVector p F)) ^ (m + 1) = algebraMap _ _ y) :
    (p : WittVector p F) ∣ y := by
  have h := congrArg (WittVector.constantCoeff : WittVector p F →+* F)
    (numerator_equation p x hx (m + 1) y hy)
  have hp : (m + 1) * (p - 1) ≠ 0 := Nat.mul_ne_zero (Nat.succ_ne_zero m) (by
    have hprime := (Fact.out : p.Prime).one_lt
    omega)
  simp only [map_mul, map_pow, WittVector.constantCoeff_apply, WittVector.coeff_p_zero,
    zero_pow hp, mul_zero] at h
  apply Ideal.mem_span_singleton.mp
  exact (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr (eq_zero_of_pow_eq_zero h.symm)

theorem exists_witt_of_prime_presentation (x : FractionRing (WittVector p F))
    (hx : phi p x = x ^ p) (m : ℕ) (y : WittVector p F)
    (hy : x * (p : FractionRing (WittVector p F)) ^ m = algebraMap _ _ y) :
    ∃ a : WittVector p F, algebraMap (WittVector p F) (FractionRing (WittVector p F)) a = x := by
  induction m generalizing y with
  | zero => exact ⟨y, by simpa only [pow_zero, mul_one] using hy.symm⟩
  | succ m ih =>
    obtain ⟨b, hb⟩ := numerator_prime_dvd p x hx m y hy
    have hp : (p : FractionRing (WittVector p F)) ≠ 0 := WittVector.FractionRing.p_nonzero p F
    apply ih b
    apply mul_right_cancel₀ hp
    calc
      _ = x * (p : FractionRing (WittVector p F)) ^ (m + 1) := by rw [pow_succ, mul_assoc]
      _ = algebraMap (WittVector p F) (FractionRing (WittVector p F)) y := hy
      _ = _ := by rw [hb, map_mul, map_natCast, mul_comm]

theorem exists_teichmuller_of_prime_presentation (x : FractionRing (WittVector p F))
    (hx : phi p x = x ^ p) (m : ℕ) (y : WittVector p F)
    (hy : x * (p : FractionRing (WittVector p F)) ^ m = algebraMap _ _ y) :
    ∃ r : F, algebraMap (WittVector p F) (FractionRing (WittVector p F)) (WittVector.teichmuller p r) = x := by
  obtain ⟨a, ha⟩ := exists_witt_of_prime_presentation p x hx m y hy
  have he : WittVector.frobenius a = a ^ p := by
    apply IsFractionRing.injective (WittVector p F) (FractionRing (WittVector p F))
    rw [← phi_algebraMap, ha, hx, map_pow, ha]
  exact ⟨a.coeff 0, (congrArg (algebraMap (WittVector p F) (FractionRing (WittVector p F)))
    (WittFrobeniusTeichmullerRigidity.eq_teichmuller_of_frobenius_eq_pow p a he)).symm.trans ha⟩

end
end JoshiTeich.Act1Scene1.WittFractionFrobeniusRigidity
