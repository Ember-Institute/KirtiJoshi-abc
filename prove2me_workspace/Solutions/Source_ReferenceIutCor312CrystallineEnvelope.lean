import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltField
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
Joshi III, crystalline periods used in (9.9.4)–(9.9.6).
The divided powers of the kernel of the actual Fontaine map generate the
integral subalgebra of `Ainf[1/p]` whose p-adic completion defines `A_cris`.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

universe u
variable (C : Type u) [NormedField C] [IsUltrametricDist C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

abbrev Ainf := WittVector p (GeometricTiltField.Source C p)

abbrev AinfInvertP := Localization.Away (p : Ainf C p)

local notation "ι" => algebraMap (Ainf C p) (AinfInvertP C p)
local notation "θ" => (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))

theorem algebraMap_injective : Function.Injective ι := by
  apply IsLocalization.injective (M := Submonoid.powers (p : Ainf C p))
  rintro x ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (pow_ne_zero n (WittVector.p_nonzero p (GeometricTiltField.Source C p)))

private theorem prime_isUnit : IsUnit (p : AinfInvertP C p) := by
  simpa only [map_natCast] using
    (IsLocalization.Away.algebraMap_isUnit (S := AinfInvertP C p) (p : Ainf C p))

/-- All nonzero natural numbers become units in the p-localization of the Witt ring. -/
theorem natCast_isUnit (n : ℕ) (hn : n ≠ 0) : IsUnit (n : AinfInvertP C p) := by
  let toPadic : WittVector p (ZMod p) →+* PadicInt p := (WittVector.equiv p).toRingHom
  have hnW : (n : WittVector p (ZMod p)) ≠ 0 := by
    intro h
    have hnP : toPadic (n : WittVector p (ZMod p)) = 0 :=
      (congrArg toPadic h).trans toPadic.map_zero
    exact (Nat.cast_ne_zero.mpr hn) ((map_natCast toPadic n).symm.trans hnP)
  let f : WittVector p (ZMod p) →+* AinfInvertP C p :=
    (ι).comp (WittVector.map (ZMod.castHom (dvd_refl p) (GeometricTiltField.Source C p)))
  obtain ⟨m, v, hv⟩ := WittVector.exists_eq_pow_p_mul' (n : WittVector p (ZMod p)) hnW
  have h : IsUnit (f ((p : WittVector p (ZMod p)) ^ m * v)) := by
    rw [map_mul, map_pow, map_natCast]
    exact ((prime_isUnit C p).pow m).mul (v.isUnit.map f)
  simpa only [← hv, map_natCast] using h

/-- The element `x^n / n!` of the p-localization. -/
def gamma (n : ℕ) (x : Ainf C p) : AinfInvertP C p :=
  Ring.inverse (n.factorial : AinfInvertP C p) * (ι x) ^ n

theorem factorial_mul_gamma (n : ℕ) (x : Ainf C p) :
    (n.factorial : AinfInvertP C p) * gamma C p n x = (ι x) ^ n := by
  rw [gamma, ← mul_assoc, Ring.mul_inverse_cancel _ (natCast_isUnit C p _ n.factorial_ne_zero),
    one_mul]

variable [CompleteSpace C]

/-- The uncompleted crystalline ring inside the localization of the actual Witt ring. -/
def A0 : Subalgebra (Ainf C p) (AinfInvertP C p) :=
  Algebra.adjoin (Ainf C p) {z | ∃ n : ℕ, ∃ x ∈ RingHom.ker θ, gamma C p n x = z}

theorem algebraMap_A0_injective :
    Function.Injective (algebraMap (Ainf C p) (A0 C p)) := by
  intro a b h
  apply algebraMap_injective C p
  exact congrArg (fun y : A0 C p => (y : AinfInvertP C p)) h

theorem gamma_mem_A0 (n : ℕ) {x : Ainf C p} (hx : x ∈ RingHom.ker θ) :
    gamma C p n x ∈ A0 C p :=
  Algebra.subset_adjoin ⟨n, x, hx, rfl⟩

/-- The divided power of an element of the Fontaine kernel in the integral ring. -/
def gammaIn (n : ℕ) (x : Ainf C p) (hx : x ∈ RingHom.ker θ) : A0 C p :=
  ⟨gamma C p n x, gamma_mem_A0 C p n hx⟩

theorem factorial_mul_gammaIn (n : ℕ) (x : Ainf C p) (hx : x ∈ RingHom.ker θ) :
    (n.factorial : A0 C p) * gammaIn C p n x hx = (algebraMap (Ainf C p) (A0 C p) x) ^ n := by
  let f := (A0 C p).val
  apply Subtype.ext
  change f ((n.factorial : A0 C p) * gammaIn C p n x hx) =
    f ((algebraMap (Ainf C p) (A0 C p) x) ^ n)
  rw [map_mul, map_natCast, map_pow, f.commutes]
  exact factorial_mul_gamma C p n x

theorem prime_dvd_pow_of_mem_ker {x : Ainf C p} (hx : x ∈ RingHom.ker θ) :
    (p : A0 C p) ∣ (algebraMap (Ainf C p) (A0 C p) x) ^ p := by
  have hp : p ∣ p.factorial := Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl
  have hp' : (p : A0 C p) ∣ (p.factorial : A0 C p) := by
    simpa only [Nat.coe_castRingHom] using map_dvd (Nat.castRingHom (A0 C p)) hp
  rw [← factorial_mul_gammaIn C p p x hx]
  exact hp'.trans (dvd_mul_right _ _)

/-- A Teichmüller difference in the sum of the Fontaine kernel and the prime
ideal has p-th power divisible by p in the uncompleted crystalline ring. -/
theorem prime_dvd_pow_of_mem_ker_sup_prime {x : Ainf C p}
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) :
    (p : A0 C p) ∣ (algebraMap (Ainf C p) (A0 C p) x) ^ p := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  let f := algebraMap (Ainf C p) (A0 C p)
  let I : Ideal (A0 C p) := Ideal.span {(p : A0 C p)}
  let q := Ideal.Quotient.mk I
  have hqv : q (f v) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    simpa only [map_natCast] using map_dvd f (Ideal.mem_span_singleton.mp hv)
  have hqu : q (f u ^ p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (prime_dvd_pow_of_mem_ker C p hu))
  have hqadd : q (f (u + v)) = q (f u) := by
    rw [map_add f, map_add q, hqv, add_zero]
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (f (u + v) ^ p) = 0
  rw [map_pow, hqadd, ← map_pow, hqu]

/-- Powers of the original Teichmüller difference tend to zero p-adically. -/
theorem prime_pow_dvd_pow_of_mem_ker_sup_prime {x : Ainf C p}
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) (m : ℕ) :
    (p : A0 C p) ^ m ∣ (algebraMap (Ainf C p) (A0 C p) x) ^ (p * m) := by
  rw [pow_mul]
  exact pow_dvd_pow_of_dvd (prime_dvd_pow_of_mem_ker_sup_prime C p hx) m

end
end JoshiTeich.Act1Scene1.CrystallineEnvelope
