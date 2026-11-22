import Solutions.Source_ReferenceIutCor312CrystallineLogNaturality
import Mathlib.RingTheory.WittVector.Complete

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "φ" => (WittVector.frobenius : Ainf C p →+* Ainf C p)
local notation "θ" => (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))

omit [CompleteSpace C] in
private theorem frobenius_sub_pow_mem_prime (x : Ainf C p) :
    φ x - x ^ p ∈ Ideal.span {(p : Ainf C p)} := by
  apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
  let c : Ainf C p →+* GeometricTiltField.Source C p := WittVector.constantCoeff
  change c (φ x - x ^ p) = 0
  rw [map_sub, map_pow, sub_eq_zero]
  exact WittVector.coeff_frobenius_charP p x 0

theorem frobenius_mem_kerSupPrime {x : Ainf C p} (hx : x ∈ kerSupPrime C p) :
    φ x ∈ kerSupPrime C p := by
  have hle : Ideal.span {(p : Ainf C p)} ≤ kerSupPrime C p := le_sup_right
  have hdiff : φ x - x ^ p ∈ kerSupPrime C p :=
    hle (frobenius_sub_pow_mem_prime C p x)
  have hpow : x ^ p ∈ kerSupPrime C p :=
    (kerSupPrime C p).pow_mem_of_mem hx p (Fact.out : p.Prime).pos
  rw [← sub_add_cancel (φ x) (x ^ p)]
  exact (kerSupPrime C p).add_mem hdiff hpow

private theorem frobenius_mem_kerSupPrime_of_mem_ker (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ) : φ x ∈ kerSupPrime C p := by
  have hle : RingHom.ker θ ≤ kerSupPrime C p := le_sup_left
  exact frobenius_mem_kerSupPrime C p (hle hx)

/-- The restriction of the localized Witt Frobenius to the integral crystalline subalgebra. -/
def frobeniusA0 : A0 C p →+* A0 C p :=
  mapA0 C p φ (frobenius_mem_kerSupPrime_of_mem_ker C p)

/-- The Witt Frobenius on the p-adic completion of the integral crystalline subalgebra. -/
def frobeniusACris : ACris C p →+* ACris C p :=
  mapACris C p (frobeniusA0 C p)

@[simp]
theorem frobeniusACris_algebraMap (x : Ainf C p) :
    frobeniusACris C p (algebraMap (A0 C p) (ACris C p)
      (algebraMap (Ainf C p) (A0 C p) x)) =
    algebraMap (A0 C p) (ACris C p) (algebraMap (Ainf C p) (A0 C p) (φ x)) := by
  rw [frobeniusACris, mapACris_algebraMap, frobeniusA0, mapA0_algebraMap]

theorem frobeniusACris_logOfMemKerSupPrime {x : Ainf C p} (hx : x ∈ kerSupPrime C p)
    (hφx : φ x ∈ kerSupPrime C p) :
    frobeniusACris C p (logOfMemKerSupPrime C p x hx) =
      logOfMemKerSupPrime C p (φ x) hφx :=
  mapACris_logOfMemKerSupPrime C p φ (frobenius_mem_kerSupPrime_of_mem_ker C p) hx hφx rfl

/-- Frobenius carries the crystalline logarithm of a cyclotomic tower to
the crystalline logarithm of the pointwise p-th power of that tower. -/
theorem frobeniusACris_cyclotomicLog (ε : LocalKummer.cyclotomicTateGroup p C) :
    frobeniusACris C p (cyclotomicLog C p ε) = cyclotomicLog C p (ε ^ p) := by
  unfold frobeniusACris frobeniusA0 cyclotomicLog
  apply mapACris_logOfMemKerSupPrime
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller, _root_.frobenius_def, (CyclotomicTateTilt.toPreTilt C p).map_pow]

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
