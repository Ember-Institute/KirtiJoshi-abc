import Solutions.Source_ReferenceIutCor312KummerCrystallineBridge
import Solutions.Source_ReferenceIutCor312DividedPowerLogBinomial

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝔦" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))
local notation "ι" => algebraMap (Ainf C p) (A0 C p)

/-- The finite binomial approximation to the crystalline logarithm of `1 + x`. -/
def logBinomial (x : Ainf C p) (hx : x ∈ kerSupPrime C p) (N : ℕ) : A0 C p :=
  DividedPowerLog.binomialApproximation (fun n => gammaInOfMemKerSupPrime C p n x hx) (N - 1)

theorem exponent_mul_logBinomial
    (x : Ainf C p) (hx : x ∈ kerSupPrime C p) (N : ℕ) (hN : 0 < N) :
    (N : A0 C p) * logBinomial C p x hx N = (1 + ι x) ^ N - 1 := by
  simpa only [logBinomial, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN.ne')] using
    (DividedPowerLog.succ_mul_binomialApproximation
      (fun n => gammaInOfMemKerSupPrime C p n x hx)
      (fun n => factorial_mul_gammaInOfMemKerSupPrime C p n x hx) (N - 1))

private theorem logBinomial_pow
    (x y : Ainf C p) (hx : x ∈ kerSupPrime C p) (hy : y ∈ kerSupPrime C p)
    (r N : ℕ) (hr : 0 < r) (hN : 0 < N) (hxy : 1 + y = (1 + x) ^ r) :
    logBinomial C p y hy N = (r : A0 C p) * logBinomial C p x hx (r * N) := by
  let j := (A0 C p).val
  have hj : Function.Injective j := Subtype.val_injective
  have hyx : 1 + ι y = (1 + ι x) ^ r := by
    simpa only [map_add, map_one, map_pow] using congrArg ι hxy
  have hmul :
      (N : A0 C p) * logBinomial C p y hy N =
        (N : A0 C p) * ((r : A0 C p) * logBinomial C p x hx (r * N)) := by
    calc
      _ = (1 + ι y) ^ N - 1 := exponent_mul_logBinomial C p y hy N hN
      _ = (1 + ι x) ^ (r * N) - 1 := by rw [hyx, pow_mul]
      _ = ((r * N : ℕ) : A0 C p) * logBinomial C p x hx (r * N) :=
        (exponent_mul_logBinomial C p x hx (r * N) (Nat.mul_pos hr hN)).symm
      _ = _ := by rw [Nat.cast_mul, ← mul_assoc, mul_comm (r : A0 C p)]
  apply hj
  apply (natCast_isUnit C p N hN.ne').mul_left_cancel
  simpa only [map_mul, map_natCast] using congrArg j hmul

theorem eval_log_eq_logBinomial
    (x : Ainf C p) (hx : x ∈ kerSupPrime C p)
    {k N : ℕ} (hN : 0 < N) (hcut : p * k ≤ N) (hdiv : p ^ k ∣ N) :
    AdicCompletion.evalₐ 𝔦 k (logOfMemKerSupPrime C p x hx) =
      Ideal.Quotient.mk (𝔦 ^ k) (logBinomial C p x hx N) := by
  let γ : ℕ → A0 C p := fun i => gammaInOfMemKerSupPrime C p i x hx
  have hmem : (N : A0 C p) ∈ 𝔦 ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simpa only [Nat.coe_castRingHom, Nat.cast_pow] using
      map_dvd (Nat.castRingHom (A0 C p)) hdiv
  have hq := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have he : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN.ne')
  have hmod : Ideal.Quotient.mk (𝔦 ^ k) (((N - 1 + 1 : ℕ) : A0 C p)) = 0 := by
    rw [he]
    exact hq
  calc
    _ = Ideal.Quotient.mk (𝔦 ^ k) (DividedPowerLog.logPartialSum γ N) :=
      eval_logOfMemKerSupPrime C p x hx hcut
    _ = _ := by
      simpa only [he, logBinomial, γ] using
        (DividedPowerLog.quotient_binomialApproximation_eq_logPartialSum (𝔦 ^ k) hmod γ).symm

private theorem eval_natCast_mul_of_eq_mk {R : Type*} [CommRing R]
    (J : Ideal R) (k r : ℕ) {x : AdicCompletion J R} {a : R}
    (hx : AdicCompletion.evalₐ J k x = Ideal.Quotient.mk (J ^ k) a) :
    AdicCompletion.evalₐ J k ((r : AdicCompletion J R) * x) =
      Ideal.Quotient.mk (J ^ k) ((r : R) * a) := by
  simp only [map_mul, map_natCast, hx]

private theorem eval_logOfMemKerSupPrime_pow
    (x y : Ainf C p) (hx : x ∈ kerSupPrime C p) (hy : y ∈ kerSupPrime C p)
    (r : ℕ) (hr : 0 < r) (hxy : 1 + y = (1 + x) ^ r) (k : ℕ) :
    AdicCompletion.evalₐ 𝔦 k (logOfMemKerSupPrime C p y hy) =
      AdicCompletion.evalₐ 𝔦 k ((r : ACris C p) * logOfMemKerSupPrime C p x hx) := by
  let N : ℕ := p ^ k
  have hN : 0 < N := pow_pos (Fact.out : p.Prime).pos _
  have hcut : p * k ≤ N := Nat.mul_le_pow (Fact.out : p.Prime).ne_one k
  have hNr : N ≤ r * N := by
    simpa only [one_mul] using Nat.mul_le_mul_right N (Nat.one_le_iff_ne_zero.mpr hr.ne')
  have hdiv : p ^ k ∣ r * N := dvd_mul_left N r
  have hyk := eval_log_eq_logBinomial C p y hy (k := k) (N := N) hN hcut (dvd_refl N)
  have hxk := eval_log_eq_logBinomial C p x hx (k := k) (N := r * N)
    (Nat.mul_pos hr hN) (hcut.trans hNr) hdiv
  have hpow := logBinomial_pow C p x y hx hy r N hr hN hxy
  calc
    _ = Ideal.Quotient.mk (𝔦 ^ k) (logBinomial C p y hy N) := hyk
    _ = Ideal.Quotient.mk (𝔦 ^ k) ((r : A0 C p) * logBinomial C p x hx (r * N)) :=
      congrArg (Ideal.Quotient.mk (𝔦 ^ k)) hpow
    _ = _ := (eval_natCast_mul_of_eq_mk 𝔦 k r hxk).symm

/-- The logarithm of a positive integral power in the same crystalline ring. -/
theorem logOfMemKerSupPrime_pow
    (x y : Ainf C p) (hx : x ∈ kerSupPrime C p) (hy : y ∈ kerSupPrime C p)
    (r : ℕ) (hr : 0 < r) (hxy : 1 + y = (1 + x) ^ r) :
    logOfMemKerSupPrime C p y hy = (r : ACris C p) * logOfMemKerSupPrime C p x hx :=
  AdicCompletion.ext_evalₐ (I := 𝔦) (eval_logOfMemKerSupPrime_pow C p x y hx hy r hr hxy)

/-- The logarithm of a cyclotomic tower raised to the p-th power is p times
the logarithm of the original tower. -/
theorem cyclotomicLog_pow_prime (ε : LocalKummer.cyclotomicTateGroup p C) :
    cyclotomicLog C p (ε ^ p) = (p : ACris C p) * cyclotomicLog C p ε := by
  unfold cyclotomicLog
  apply logOfMemKerSupPrime_pow C p _ _ _ _ p (Fact.out : p.Prime).pos
  have h (z : Ainf C p) : 1 + (z - 1) = z :=
    (add_comm _ _).trans (sub_add_cancel _ _)
  simp only [h, map_pow]

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
