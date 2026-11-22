import Solutions.Source_ReferenceIutCor312CrystallineLogPower
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝔦" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))
local notation "ι" => algebraMap (Ainf C p) (A0 C p)

private theorem logBinomial_mul
    (x y z : Ainf C p) (hx : x ∈ kerSupPrime C p) (hy : y ∈ kerSupPrime C p)
    (hz : z ∈ kerSupPrime C p) (N : ℕ) (hN : 0 < N)
    (hxyz : 1 + z = (1 + x) * (1 + y)) :
    logBinomial C p z hz N =
      logBinomial C p x hx N + logBinomial C p y hy N +
        (N : A0 C p) * logBinomial C p x hx N * logBinomial C p y hy N := by
  let a := logBinomial C p x hx N
  let b := logBinomial C p y hy N
  have hprod : 1 + ι z = (1 + ι x) * (1 + ι y) := by
    simpa only [map_add, map_mul, map_one] using congrArg ι hxyz
  have ha : (1 + ι x) ^ N = (N : A0 C p) * a + 1 :=
    sub_eq_iff_eq_add.mp (exponent_mul_logBinomial C p x hx N hN).symm
  have hb : (1 + ι y) ^ N = (N : A0 C p) * b + 1 :=
    sub_eq_iff_eq_add.mp (exponent_mul_logBinomial C p y hy N hN).symm
  have hmul : (N : A0 C p) * logBinomial C p z hz N =
      (N : A0 C p) * (a + b + (N : A0 C p) * a * b) := by
    rw [exponent_mul_logBinomial C p z hz N hN, hprod, mul_pow, ha, hb]
    ring
  let j := (A0 C p).val
  have hj : Function.Injective j := Subtype.val_injective
  apply hj
  apply (natCast_isUnit C p N hN.ne').mul_left_cancel
  simpa only [map_mul, map_natCast] using congrArg j hmul

private theorem eval_add_of_eq_mk {R : Type*} [CommRing R]
    (J : Ideal R) (k N : ℕ) {x y : AdicCompletion J R} {a b : R}
    (hx : AdicCompletion.evalₐ J k x = Ideal.Quotient.mk (J ^ k) a)
    (hy : AdicCompletion.evalₐ J k y = Ideal.Quotient.mk (J ^ k) b)
    (hN : Ideal.Quotient.mk (J ^ k) (N : R) = 0) :
    AdicCompletion.evalₐ J k (x + y) =
      Ideal.Quotient.mk (J ^ k) (a + b + (N : R) * a * b) := by
  simp only [map_add, map_mul, hx, hy, hN, zero_mul, add_zero]

private theorem eval_logOfMemKerSupPrime_mul
    (x y z : Ainf C p) (hx : x ∈ kerSupPrime C p) (hy : y ∈ kerSupPrime C p)
    (hz : z ∈ kerSupPrime C p) (hxyz : 1 + z = (1 + x) * (1 + y)) (k : ℕ) :
    AdicCompletion.evalₐ 𝔦 k (logOfMemKerSupPrime C p z hz) =
      AdicCompletion.evalₐ 𝔦 k
        (logOfMemKerSupPrime C p x hx + logOfMemKerSupPrime C p y hy) := by
  let N : ℕ := p ^ k
  have hN : 0 < N := pow_pos (Fact.out : p.Prime).pos _
  have hcut : p * k ≤ N := Nat.mul_le_pow (Fact.out : p.Prime).ne_one k
  have hNzero : Ideal.Quotient.mk (𝔦 ^ k) (N : A0 C p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simpa only [N, Nat.cast_pow] using dvd_refl ((p : A0 C p) ^ k)
  have hxk := eval_log_eq_logBinomial C p x hx (k := k) (N := N) hN hcut (dvd_refl N)
  have hyk := eval_log_eq_logBinomial C p y hy (k := k) (N := N) hN hcut (dvd_refl N)
  have hzk := eval_log_eq_logBinomial C p z hz (k := k) (N := N) hN hcut (dvd_refl N)
  have hmul := logBinomial_mul C p x y z hx hy hz N hN hxyz
  calc
    _ = Ideal.Quotient.mk (𝔦 ^ k) (logBinomial C p z hz N) := hzk
    _ = Ideal.Quotient.mk (𝔦 ^ k)
          (logBinomial C p x hx N + logBinomial C p y hy N +
            (N : A0 C p) * logBinomial C p x hx N * logBinomial C p y hy N) :=
      congrArg (Ideal.Quotient.mk (𝔦 ^ k)) hmul
    _ = _ := (eval_add_of_eq_mk 𝔦 k N hxk hyk hNzero).symm

/-- The crystalline logarithm sends a product of the form `(1 + x) * (1 + y)`
to the sum of the two logarithms. -/
theorem logOfMemKerSupPrime_mul
    (x y z : Ainf C p) (hx : x ∈ kerSupPrime C p) (hy : y ∈ kerSupPrime C p)
    (hz : z ∈ kerSupPrime C p) (hxyz : 1 + z = (1 + x) * (1 + y)) :
    logOfMemKerSupPrime C p z hz =
      logOfMemKerSupPrime C p x hx + logOfMemKerSupPrime C p y hy :=
  AdicCompletion.ext_evalₐ (I := 𝔦) (eval_logOfMemKerSupPrime_mul C p x y z hx hy hz hxyz)

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
