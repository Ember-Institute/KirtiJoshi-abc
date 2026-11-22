import Solutions.Source_ReferenceIutCor312CrystallineFontaineKernel

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

private theorem prime_pow_dvd_map_of_sub_pow_mul {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p k : ℕ) (u w v : R) (hu : (p : S) ^ k ∣ f u ^ (p * k))
    (h : (p : R) ^ k ∣ w - u ^ (p * k) * v) : (p : S) ^ k ∣ f w := by
  have hsub : (p : S) ^ k ∣ f w - f u ^ (p * k) * f v := by
    simpa only [map_sub, map_mul, map_pow, map_natCast] using (map_dvd f h)
  have hmul : (p : S) ^ k ∣ f u ^ (p * k) * f v :=
    hu.trans (dvd_mul_right (f u ^ (p * k)) (f v))
  exact (dvd_sub_left hmul).mp hsub

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "W" => Ainf C p
local notation "D" => A0 C p
local notation "θ" =>
  (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))
local notation "J" => (RingHom.ker θ ⊔ Ideal.span {(p : W)})

/-- A Witt vector congruent to a multiple of `u^(p*k)` modulo `p^k` becomes
divisible by `p^k` in the divided-power subalgebra when `u` is in the sum
of the Fontaine kernel and the prime ideal. -/
theorem prime_pow_dvd_algebraMap_of_sub_pow_mul
    (k : ℕ) (u w v : W) (hu : u ∈ J)
    (h : (p : W) ^ k ∣ w - u ^ (p * k) * v) :
    (p : D) ^ k ∣ algebraMap W D w :=
  prime_pow_dvd_map_of_sub_pow_mul (algebraMap W D) p k u w v
    (prime_pow_dvd_pow_of_mem_ker_sup_prime C p hu k) h

variable [IsAlgClosed C]

/-- The Teichmüller lift of the chosen tilt of the prime belongs to the sum of
the Fontaine kernel and the prime ideal. -/
theorem teichmuller_primeTilt_mem_ker_sup_prime :
    WittVector.teichmuller p (primeTilt C p) ∈ J := by
  have hsum : fontainePrimitive C p + (p : W) ∈ J :=
    Submodule.mem_sup.mpr
      ⟨fontainePrimitive C p, fontainePrimitive_mem_ker C p,
        (p : W), Ideal.mem_span_singleton_self _, rfl⟩
  have heq : fontainePrimitive C p + (p : W) = WittVector.teichmuller p (primeTilt C p) :=
    sub_add_cancel (WittVector.teichmuller p (primeTilt C p)) (p : W)
  exact Eq.mp (congrArg (fun a : W => a ∈ J) heq) hsum

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
