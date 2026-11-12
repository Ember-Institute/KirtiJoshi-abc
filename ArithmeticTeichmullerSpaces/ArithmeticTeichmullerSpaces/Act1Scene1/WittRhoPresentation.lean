import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.Data.ENNReal.Inv

/-!
source-id: JT-SCENE1-WITT-RHO-PRESENTATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the
presentation of a bounded Witt element by a p-power denominator.
fidelity: supplies generic algebraic presentation and quotient identities;
the coefficient value and the choice of bounded carrier remain parameters.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.WittRhoPresentation

open scoped ENNReal
noncomputable section

structure Presentation (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) (z : S) where
  exponent : ℕ
  numerator : R
  relation : z * (p : S) ^ exponent = algebraMap R S numerator

theorem numerator_cross_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsFractionRing R S]
    (p : ℕ) (z : S) (m k : ℕ) (y t : R)
    (hy : z * (p : S) ^ m = algebraMap R S y)
    (ht : z * (p : S) ^ k = algebraMap R S t) :
    y * (p : R) ^ k = t * (p : R) ^ m := by
  apply IsFractionRing.injective R S
  simp only [map_mul, map_pow, map_natCast]
  rw [← hy, ← ht]
  exact mul_right_comm z _ _

theorem quotient_independent {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsFractionRing R S]
    (p : ℕ) (v : R → ℝ≥0∞) (ρ : ℝ≥0∞)
    (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (hscale : ∀ y n, v (y * (p : R) ^ n) = ρ ^ n * v y)
    (z : S) (m k : ℕ) (y t : R)
    (hy : z * (p : S) ^ m = algebraMap R S y)
    (ht : z * (p : S) ^ k = algebraMap R S t) :
    v y / ρ ^ m = v t / ρ ^ k := by
  apply (ENNReal.div_eq_div_iff (pow_ne_zero k hρ0) (ENNReal.pow_ne_top hρtop)
    (pow_ne_zero m hρ0) (ENNReal.pow_ne_top hρtop)).mpr
  rw [← hscale y k, ← hscale t m]
  exact congrArg v (numerator_cross_eq p z m k y t hy ht)

theorem quotient_map_pow {R S : Type*}
    (v : R → ℝ≥0∞) (w : S → ℝ≥0∞) (f : R → S) (d : ℕ)
    (hv : ∀ y, w (f y) ^ d = v y) (ρ : ℝ≥0∞) (m : ℕ) (y : R) :
    (w (f y) / ρ ^ m) ^ d = v y / (ρ ^ d) ^ m := by
  rw [div_eq_mul_inv, mul_pow, hv, div_eq_mul_inv, ENNReal.inv_pow]
  congr 1
  calc
    (ρ⁻¹ ^ m) ^ d = ((ρ ^ m)⁻¹) ^ d :=
      congrArg (fun q : ℝ≥0∞ => q ^ d) (ENNReal.inv_pow.symm)
    _ = ((ρ ^ m) ^ d)⁻¹ := (ENNReal.inv_pow).symm
    _ = ((ρ ^ d) ^ m)⁻¹ := congrArg (fun q : ℝ≥0∞ => q⁻¹)
      ((pow_mul ρ m d).symm.trans
        ((congrArg (fun n : ℕ => ρ ^ n) (Nat.mul_comm m d)).trans (pow_mul ρ d m)))

theorem quotient_pow_of_power (a b r s : ℝ≥0∞) (d m : ℕ)
    (ha : a ^ d = b) (hr : r ^ d = s) :
    (a / r ^ m) ^ d = b / s ^ m := by
  simpa only [hr] using
    (quotient_map_pow (fun _ : Unit => b) (fun _ : Unit => a) id d
      (fun _ => ha) r m ())


end
end JoshiTeich.Act1Scene1.WittRhoPresentation
