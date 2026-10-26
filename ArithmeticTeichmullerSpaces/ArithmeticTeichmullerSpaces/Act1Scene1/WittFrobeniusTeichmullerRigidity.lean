import Mathlib.RingTheory.WittVector.Complete
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Ring.Divisibility.Basic

/-!
source-id: JT-SCENE1-WITT-FROBENIUS-TEICHMULLER-RIGIDITY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, recognition
of Teichmuller representatives; Witt Frobenius and p-adic separation.
fidelity: over a perfect characteristic-p ring, proves phi(a)=a^p iff
a is the Teichmuller lift of its actual zeroth coefficient. The proof
uses the p-power difference congruence and pulls it back by iterated
invertible Frobenius, giving divisibility by every p-power.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the statement is on original Witt vectors.
Existence of integral lifts of annular exponentials remains separate.
-/

namespace JoshiTeich.Act1Scene1.WittFrobeniusTeichmullerRigidity

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

omit [PerfectRing R p] in
theorem frobenius_teichmuller (r : R) :
    WittVector.frobenius (WittVector.teichmuller p r) = (WittVector.teichmuller p r) ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem iterate_frobenius_eq_pow (a : WittVector p R)
    (ha : WittVector.frobenius a = a ^ p) (n : ℕ) :
    (WittVector.frobeniusEquiv p R ^ n) a = a ^ (p ^ n) := by
  induction n with
  | zero => simp only [pow_zero, RingAut.one_apply, pow_one]
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, WittVector.frobeniusEquiv_apply, ha, map_pow, ih,
      ← pow_mul, ← pow_succ]

theorem prime_dvd_sub_teichmuller (a : WittVector p R) :
    (p : WittVector p R) ∣ a - WittVector.teichmuller p (a.coeff 0) := by
  apply Ideal.mem_span_singleton.mp
  apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
  change WittVector.constantCoeff (a - WittVector.teichmuller p (a.coeff 0)) = 0
  rw [map_sub]
  exact sub_self _

theorem prime_pow_dvd_sub_teichmuller (a : WittVector p R)
    (ha : WittVector.frobenius a = a ^ p) (n : ℕ) :
    (p : WittVector p R) ^ (n + 1) ∣ a - WittVector.teichmuller p (a.coeff 0) := by
  have h := dvd_sub_pow_of_dvd_sub (prime_dvd_sub_teichmuller p a) n
  apply (map_dvd_iff (WittVector.frobeniusEquiv p R ^ n)).mp
  rw [map_pow, map_natCast, map_sub, iterate_frobenius_eq_pow p a ha,
    iterate_frobenius_eq_pow p _ (frobenius_teichmuller p _) ]
  exact h

theorem eq_teichmuller_of_frobenius_eq_pow (a : WittVector p R)
    (ha : WittVector.frobenius a = a ^ p) : a = WittVector.teichmuller p (a.coeff 0) := by
  apply sub_eq_zero.mp
  apply WittVector.ext
  intro n
  rw [WittVector.zero_coeff]
  exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).mp
    (Ideal.mem_span_singleton.mpr (prime_pow_dvd_sub_teichmuller p a ha n)) n (Nat.lt_succ_self n)

theorem frobenius_eq_pow_iff (a : WittVector p R) :
    WittVector.frobenius a = a ^ p ↔ a = WittVector.teichmuller p (a.coeff 0) := by
  constructor
  · exact eq_teichmuller_of_frobenius_eq_pow p a
  · intro h
    rw [h]
    exact frobenius_teichmuller p _

theorem existsUnique_teichmuller_of_frobenius_eq_pow (a : WittVector p R)
    (ha : WittVector.frobenius a = a ^ p) : ∃! r : R, a = WittVector.teichmuller p r := by
  refine ⟨a.coeff 0, eq_teichmuller_of_frobenius_eq_pow p a ha, ?_⟩
  intro r hr
  exact (congrArg (fun x : WittVector p R => x.coeff 0) hr).symm

end
end JoshiTeich.Act1Scene1.WittFrobeniusTeichmullerRigidity
