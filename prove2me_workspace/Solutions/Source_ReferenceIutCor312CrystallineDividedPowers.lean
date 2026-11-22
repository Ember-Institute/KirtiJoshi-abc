import Solutions.Source_ReferenceIutCor312CrystallineEnvelope
import Mathlib.RingTheory.DividedPowers.Padic

/-!
Joshi III, crystalline logarithm for (9.9.4)–(9.9.6).
Every divided power of a Witt vector in the sum of the Fontaine kernel and
the prime ideal lies in the uncompleted crystalline ring. This gives the
coefficients of the logarithm for the original Kummer root tower.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

universe u
variable (C : Type u) [NormedField C] [IsUltrametricDist C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "ι" => algebraMap (Ainf C p) (AinfInvertP C p)
local notation "θ" => (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))

theorem gamma_mul (n : ℕ) (x y : Ainf C p) :
    gamma C p n (x * y) = gamma C p n x * (ι y) ^ n := by
  simp only [gamma, map_mul, mul_pow, mul_assoc]

theorem gamma_add (n : ℕ) (x y : Ainf C p) :
    gamma C p n (x + y) = (Finset.antidiagonal n).sum
      (fun k => gamma C p k.1 x * gamma C p k.2 y) := by
  classical
  let I : Ideal (AinfInvertP C p) := ⊤
  have hn : IsUnit (((n + 1) - 1).factorial : AinfInvertP C p) := by
    simpa only [Nat.add_sub_cancel] using natCast_isUnit C p n.factorial n.factorial_ne_zero
  have hx : ι x ∈ I := Submodule.mem_top
  have hy : ι y ∈ I := Submodule.mem_top
  have h := DividedPowers.OfInvertibleFactorial.dpow_add_of_lt (n := n + 1)
    hn (Nat.lt_succ_self n) hx hy
  simpa only [I, DividedPowers.OfInvertibleFactorial.dpow, Submodule.mem_top, if_true,
    gamma, map_add] using h

variable [CompleteSpace C]

private def padicIntToAinf : PadicInt p →+* Ainf C p :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (GeometricTiltField.Source C p))).comp
    (WittVector.fromPadicInt p)

/-- The divided power of the prime comes from the p-adic integer divided powers. -/
private theorem gamma_prime_mem_A0 (n : ℕ) : gamma C p n (p : Ainf C p) ∈ A0 C p := by
  let dp := PadicInt.dividedPowers p
  let w := padicIntToAinf C p (dp.dpow n (p : PadicInt p))
  have hp : (p : PadicInt p) ∈ Ideal.span {(p : PadicInt p)} :=
    Ideal.subset_span (Set.mem_singleton _)
  have hpw : (n.factorial : PadicInt p) * dp.dpow n (p : PadicInt p) = (p : PadicInt p) ^ n :=
    dp.factorial_mul_dpow_eq_pow hp
  have hw : gamma C p n (p : Ainf C p) = ι w := by
    apply (natCast_isUnit C p n.factorial n.factorial_ne_zero).mul_left_cancel
    rw [factorial_mul_gamma]
    simpa only [w, RingHom.comp_apply, map_mul, map_natCast, map_pow] using
      (congrArg ((ι).comp (padicIntToAinf C p)) hpw).symm
  rw [hw]
  exact (A0 C p).algebraMap_mem w

theorem gamma_mem_A0_of_mem_ker_sup_prime (n : ℕ) {x : Ainf C p}
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) :
    gamma C p n x ∈ A0 C p := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hb
  rw [gamma_add]
  refine (A0 C p).sum_mem (fun k _ => (A0 C p).mul_mem (gamma_mem_A0 C p k.1 ha) ?_)
  rw [gamma_mul]
  exact (A0 C p).mul_mem (gamma_prime_mem_A0 C p k.2)
    ((A0 C p).pow_mem ((A0 C p).algebraMap_mem y) k.2)

/-- The divided power of a Teichmüller difference in the integral crystalline ring. -/
def gammaInOfMemKerSupPrime (n : ℕ) (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) : A0 C p :=
  ⟨gamma C p n x, gamma_mem_A0_of_mem_ker_sup_prime C p n hx⟩

theorem factorial_mul_gammaInOfMemKerSupPrime (n : ℕ) (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) :
    (n.factorial : A0 C p) * gammaInOfMemKerSupPrime C p n x hx =
      (algebraMap (Ainf C p) (A0 C p) x) ^ n := by
  let f := (A0 C p).val
  apply Subtype.ext
  change f ((n.factorial : A0 C p) * gammaInOfMemKerSupPrime C p n x hx) =
    f ((algebraMap (Ainf C p) (A0 C p) x) ^ n)
  rw [map_mul, map_natCast, map_pow, f.commutes]
  exact factorial_mul_gamma C p n x

end
end JoshiTeich.Act1Scene1.CrystallineEnvelope
