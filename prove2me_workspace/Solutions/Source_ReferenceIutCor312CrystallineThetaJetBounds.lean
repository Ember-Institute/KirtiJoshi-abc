import Solutions.Source_ReferenceIutCor312CrystallineFontaineKernel
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

private theorem scaled_eval_mem_range {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a d : R) (u : S) (m : ℕ)
    (hu : u ^ (m + 1) = 0) (hd : f d * u = f a) (P : Polynomial R) :
    (f d) ^ m * P.eval₂ f u ∈ f.range := by
  rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
  refine Subring.sum_mem f.range ?_
  intro n _
  by_cases hn : n ≤ m
  · refine RingHom.mem_range.mpr ⟨P.coeff n * d ^ (m - n) * a ^ n, ?_⟩
    calc
      _ = f (P.coeff n) * (f d ^ (m - n) * f a ^ n) := by
        simp only [map_mul, map_pow, mul_assoc]
      _ = f (P.coeff n) * (f d ^ (m - n) * (f d ^ n * u ^ n)) := by
        rw [← hd, mul_pow]
      _ = _ := by
        rw [← mul_assoc (f d ^ (m - n)), ← pow_add, Nat.sub_add_cancel hn]
        ac_rfl
  · rw [pow_eq_zero_of_le (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)) hu, mul_zero, mul_zero]
    exact Subring.zero_mem _

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "A" => Ainf C p
local notation "B" => AinfInvertP C p
local notation "ι" => algebraMap A B
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))
local notation "ξ" => fontainePrimitive C p

/-- The ideal defining the quotient at order `m + 1` of the localized Fontaine kernel. -/
def thetaJetIdeal (m : ℕ) : Ideal B := Ideal.span {(ι ξ) ^ (m + 1)}

local notation "J" => thetaJetIdeal C p
local notation "Q" => fun m : ℕ => B ⧸ J m
local notation "q" => fun m : ℕ => Ideal.Quotient.mk (J m)

private def scaledPrimitive (m : ℕ) : B :=
  Ring.inverse (m.factorial : B) * ι ξ

private theorem thetaJet_primitive_pow_eq_zero (m : ℕ) : (q m (ι ξ)) ^ (m + 1) = 0 := by
  have h : q m ((ι ξ) ^ (m + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  exact (map_pow (q m) (ι ξ) (m + 1)).symm.trans h

private theorem thetaJet_scaledPrimitive_nilpotent (m : ℕ) :
    (q m (scaledPrimitive C p m)) ^ (m + 1) = 0 := by
  rw [scaledPrimitive, map_mul (q m), mul_pow, thetaJet_primitive_pow_eq_zero, mul_zero]

private theorem thetaJet_mul_scaledPrimitive (m : ℕ) :
    (m.factorial : Q m) * q m (scaledPrimitive C p m) = q m (ι ξ) := by
  have h : (m.factorial : B) * scaledPrimitive C p m = ι ξ := by
    rw [scaledPrimitive, ← mul_assoc,
      Ring.mul_inverse_cancel _ (natCast_isUnit C p _ m.factorial_ne_zero), one_mul]
  simpa only [map_natCast, map_mul] using congrArg (q m) h

private theorem thetaJet_factorial_mul_gamma (m n : ℕ) (x : A) :
    (n.factorial : Q m) * q m (gamma C p n x) = (q m (ι x)) ^ n := by
  simpa only [map_mul, map_pow, map_natCast] using congrArg (q m) (factorial_mul_gamma C p n x)

private theorem thetaJet_gamma_eq_zero
    (m n : ℕ) (hn : m < n) (x : A) (hx : x ∈ RingHom.ker θ) :
    q m (gamma C p n x) = 0 := by
  rw [fontaineKernel_eq_span C p, Ideal.mem_span_singleton] at hx
  obtain ⟨b, hb⟩ := hx
  have h : IsUnit (n.factorial : Q m) := by
    simpa only [map_natCast] using (natCast_isUnit C p _ n.factorial_ne_zero).map (q m)
  apply h.mul_left_cancel
  rw [mul_zero, thetaJet_factorial_mul_gamma]
  have hd : q m (ι ξ) ^ n = 0 :=
    pow_eq_zero_of_le (Nat.succ_le_of_lt hn) (thetaJet_primitive_pow_eq_zero C p m)
  rw [hb, map_mul ι, map_mul (q m), mul_pow, hd, zero_mul]

private theorem thetaJet_gamma_eq_scaled_pow
    (m n : ℕ) (hn : n ≤ m) (x : A) (hx : x ∈ RingHom.ker θ) :
    ∃ b : A, q m (gamma C p n x) = q m (ι b) * (q m (scaledPrimitive C p m)) ^ n := by
  rw [fontaineKernel_eq_span C p, Ideal.mem_span_singleton] at hx
  obtain ⟨b, hb⟩ := hx
  have hdiv : n.factorial ∣ m.factorial ^ n := by
    cases n with
    | zero => simp only [Nat.factorial_zero, one_dvd]
    | succ n =>
        exact (Nat.factorial_dvd_factorial hn).trans (dvd_pow_self _ (Nat.succ_ne_zero n))
  obtain ⟨r, hr⟩ := hdiv
  have hr' : (m.factorial : Q m) ^ n = (n.factorial : Q m) * (r : Q m) := by
    simpa only [Nat.cast_pow, Nat.cast_mul] using congrArg (fun k : ℕ => (k : Q m)) hr
  have hunit : IsUnit (n.factorial : Q m) := by
    simpa only [map_natCast] using (natCast_isUnit C p _ n.factorial_ne_zero).map (q m)
  refine ⟨(r : A) * b ^ n, hunit.mul_left_cancel ?_⟩
  rw [thetaJet_factorial_mul_gamma, hb]
  simp only [map_mul, map_pow, map_natCast]
  rw [← thetaJet_mul_scaledPrimitive C p m, mul_pow, mul_pow, hr']
  ac_rfl

/-- In the quotient by the `(m + 1)`-st power of the localized Fontaine kernel,
multiplying any element of the integral divided-power ring by `(m!)^m`
clears its denominators. -/
theorem thetaJet_exists_scaled_ainf (m : ℕ) (z : A0 C p) :
    ∃ a : A, q m ((m.factorial : B) ^ m * (z : B)) = q m (ι a) := by
  let f : A →+* Q m := (q m).comp ι
  letI : Algebra A (Q m) := f.toAlgebra
  let u : Q m := q m (scaledPrimitive C p m)
  let S : Subalgebra A (Q m) := Algebra.adjoin A {u}
  have hs : u ∈ S := Algebra.subset_adjoin rfl
  have hz : q m (z : B) ∈ S := by
    refine Algebra.adjoin_induction (p := fun y _ => q m y ∈ S) ?_ ?_ ?_ ?_ z.2
    · rintro _ ⟨n, x, hx, rfl⟩
      by_cases h : n ≤ m
      · obtain ⟨b, hb⟩ := thetaJet_gamma_eq_scaled_pow C p m n h x hx
        rw [hb]
        exact S.mul_mem (S.algebraMap_mem b) (S.pow_mem hs n)
      · rw [thetaJet_gamma_eq_zero C p m n (Nat.lt_of_not_ge h) x hx]
        exact S.zero_mem
    · exact S.algebraMap_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact S.add_mem hx hy
    · intro x y _ _ hx hy
      rw [map_mul]
      exact S.mul_mem hx hy
  change q m (z : B) ∈ Algebra.adjoin A {u} at hz
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨P, hP⟩ := hz
  have he : P.eval₂ f u = q m (z : B) := hP
  have hd : f (m.factorial : A) * u = f ξ := by
    change q m (ι (m.factorial : A)) * q m (scaledPrimitive C p m) = q m (ι ξ)
    rw [map_natCast ι, map_natCast (q m)]
    exact thetaJet_mul_scaledPrimitive C p m
  have hb := scaled_eval_mem_range f ξ (m.factorial : A) u m
    (thetaJet_scaledPrimitive_nilpotent C p m) hd P
  have hq : q m ((m.factorial : B) ^ m * (z : B)) ∈ f.range := by
    simpa only [he, map_natCast, map_mul, map_pow] using hb
  obtain ⟨a, ha⟩ := RingHom.mem_range.mp hq
  exact ⟨a, ha.symm⟩

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
