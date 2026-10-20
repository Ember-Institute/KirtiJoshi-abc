import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
source-id: JT-SCENE1-WITT-TEICHMULLER-EXPANSION
source: Joshi II se:ff-rings / W(O_F) into B; Mathlib TeichmullerSeries.
fidelity: expresses an actual Witt expansion by its finite p-adic
remainders, recovers every Witt coefficient and proves uniqueness.
Proves naturality and Teichmuller scaling of these same expansions.
No analytic rho norm or completion is asserted. Original proofs;
Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.WittTeichmullerExpansion

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {R S : Type*} [CommRing R] [CharP R p] [CommRing S] [CharP S p]

def partialSum (c : ℕ → R) (N : ℕ) : WittVector p R :=
  ∑ i ∈ Finset.Iic N, WittVector.teichmuller p (c i) * (p : WittVector p R) ^ i

theorem partialSum_coeff (c : ℕ → R) (N n : ℕ) (hn : n ≤ N) :
    (partialSum p c N).coeff n = c n ^ (p ^ n) := by
  unfold partialSum
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · rw [Finset.sum_eq_single n]
    · exact WittVector.teichmuller_mul_pow_coeff n (c n)
    · intro i _ hi
      exact WittVector.teichmuller_mul_pow_coeff_of_ne (c i) hi.symm
    · intro h
      exact (h (Finset.mem_Iic.mpr hn)).elim
  · intro m
    constructor
    intro a b
    apply Subtype.ext
    have ha : a.1 = m := by
      by_contra h
      exact a.2.2 (WittVector.teichmuller_mul_pow_coeff_of_ne (c a.1) (fun he => h he.symm))
    have hb : b.1 = m := by
      by_contra h
      exact b.2.2 (WittVector.teichmuller_mul_pow_coeff_of_ne (c b.1) (fun he => h he.symm))
    exact ha.trans hb.symm

def Expands (x : WittVector p R) (c : ℕ → R) : Prop :=
  ∀ N : ℕ, (p : WittVector p R) ^ (N + 1) ∣ x - partialSum p c N

theorem expands_iff_coeff [PerfectRing R p] (x : WittVector p R) (c : ℕ → R) :
    Expands p x c ↔ ∀ n : ℕ, x.coeff n = c n ^ (p ^ n) := by
  constructor
  · intro h n
    have hdiv := h n
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero,
      ← WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero] at hdiv
    exact (hdiv n (Nat.lt_succ_self n)).trans (partialSum_coeff p c n n le_rfl)
  · intro h N
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero,
      ← WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
    intro n hn
    rw [h n, partialSum_coeff p c N n (Nat.lt_succ_iff.mp hn)]

def digits [PerfectRing R p] (x : WittVector p R) (n : ℕ) : R :=
  (((_root_.frobeniusEquiv R p).symm ^ n) (x.coeff n))

theorem expands_digits [PerfectRing R p] (x : WittVector p R) : Expands p x (digits p x) :=
  WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x

theorem expansion_unique [PerfectRing R p] (x y : WittVector p R) (c : ℕ → R)
    (hx : Expands p x c) (hy : Expands p y c) : x = y := by
  apply WittVector.ext
  intro n
  exact ((expands_iff_coeff p x c).mp hx n).trans ((expands_iff_coeff p y c).mp hy n).symm

theorem digits_unique [PerfectRing R p] (x : WittVector p R) (c : ℕ → R)
    (hx : Expands p x c) : c = digits p x := by
  funext n
  have h := ((expands_iff_coeff p x c).mp hx n).symm.trans
    ((expands_iff_coeff p x (digits p x)).mp (expands_digits p x) n)
  have he : c n ^ (p ^ n) = digits p x n ^ (p ^ n) := h
  have hF : ((_root_.frobeniusEquiv R p) ^ n) (c n) =
      ((_root_.frobeniusEquiv R p) ^ n) (digits p x n) := by
    simpa only [← iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_def] using he
  exact ((_root_.frobeniusEquiv R p) ^ n).injective hF

omit [CharP R p] [CharP S p] in
theorem partialSum_map (f : R →+* S) (c : ℕ → R) (N : ℕ) :
    WittVector.map f (partialSum p c N) = partialSum p (fun n => f (c n)) N := by
  simp only [partialSum, map_sum, map_mul, WittVector.map_teichmuller, map_pow, map_natCast]

omit [CharP R p] [CharP S p] in
theorem expands_map (f : R →+* S) (x : WittVector p R) (c : ℕ → R)
    (hx : Expands p x c) : Expands p (WittVector.map f x) (fun n => f (c n)) := by
  intro N
  have h := map_dvd (WittVector.map f) (hx N)
  simpa only [map_pow, map_natCast, map_sub, partialSum_map] using h

omit [CharP R p] in
theorem partialSum_teichmuller_mul (r : R) (c : ℕ → R) (N : ℕ) :
    WittVector.teichmuller p r * partialSum p c N = partialSum p (fun n => r * c n) N := by
  simp only [partialSum, Finset.mul_sum, map_mul, mul_assoc]

omit [CharP R p] in
theorem expands_teichmuller_mul (r : R) (x : WittVector p R) (c : ℕ → R)
    (hx : Expands p x c) :
    Expands p (WittVector.teichmuller p r * x) (fun n => r * c n) := by
  intro N
  rw [← partialSum_teichmuller_mul, ← mul_sub]
  exact (hx N).mul_left _

end
end JoshiTeich.Act1Scene1.WittTeichmullerExpansion
