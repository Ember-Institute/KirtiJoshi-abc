import Solutions.Source_ReferenceIutCor312CrystallineFrobenius
import Solutions.Source_ReferenceIutCor312CrystallineLogPower

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

/-- Frobenius multiplies the crystalline logarithm of a cyclotomic tower by p. -/
theorem frobeniusACris_cyclotomicLog_eq_prime_mul
    (ε : LocalKummer.cyclotomicTateGroup p C) :
    frobeniusACris C p (cyclotomicLog C p ε) = (p : ACris C p) * cyclotomicLog C p ε :=
  (frobeniusACris_cyclotomicLog C p ε).trans (cyclotomicLog_pow_prime C p ε)

local notation "φ" => (WittVector.frobenius : Ainf C p →+* Ainf C p)

private theorem frobeniusACris_log_teichmullerSubOne_eq_prime_mul
    (u : GeometricTiltField.Source C p) (hx : teichmullerSubOne C p u ∈ kerSupPrime C p) :
    frobeniusACris C p (logOfMemKerSupPrime C p (teichmullerSubOne C p u) hx) =
      (p : ACris C p) * logOfMemKerSupPrime C p (teichmullerSubOne C p u) hx := by
  let x := teichmullerSubOne C p u
  have hφx : φ x ∈ kerSupPrime C p := frobenius_mem_kerSupPrime C p hx
  have hx1 : 1 + x = WittVector.teichmuller p u := by
    change 1 + (WittVector.teichmuller p u - 1) = WittVector.teichmuller p u
    exact (add_comm _ _).trans (sub_add_cancel _ _)
  have hteich : φ (WittVector.teichmuller p u) = (WittVector.teichmuller p u) ^ p := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      _root_.frobenius_def, map_pow]
  have hpow : 1 + φ x = (1 + x) ^ p := by
    calc
      1 + φ x = φ (1 + x) := by rw [map_add, map_one]
      _ = (1 + x) ^ p := by rw [hx1, hteich]
  exact (frobeniusACris_logOfMemKerSupPrime C p hx hφx).trans
    (logOfMemKerSupPrime_pow C p x (φ x) hx hφx p (Fact.out : p.Prime).pos hpow)

/-- Frobenius multiplies the crystalline logarithm of the original Kummer
tower of a principal unit by p. -/
theorem frobeniusACris_kummerLogOfExists_eq_prime_mul
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed C]
    {a : K} (R : LocalKummer.RootTower (Ω := Ω) p a) (j : Ω →+* C)
    (ha : ‖j (algebraMap K Ω a)‖ ≤ 1)
    (hu : ∃ r : LocalGeometricFontaine.integerRing C,
      j (algebraMap K Ω a) = 1 + (p : C) * (r : C)) :
    frobeniusACris C p (kummerLogOfExists C p R j ha hu) =
      (p : ACris C p) * kummerLogOfExists C p R j ha hu :=
  frobeniusACris_log_teichmullerSubOne_eq_prime_mul C p (R.toGeometricPreTilt j ha)
    (kummerTeichmullerSubOne_mem_kerSupPrime C p R j ha hu)

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
