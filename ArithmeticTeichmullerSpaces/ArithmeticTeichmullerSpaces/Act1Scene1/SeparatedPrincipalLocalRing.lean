import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
source-id: JT-SCENE1-SEPARATED-PRINCIPAL-LOCAL-DVR
source: Mathlib adic separation and the unit-times-uniformizer-power DVR
criterion; Joshi II's de Rham period ring (1069--1076).
fidelity: a separated local ring with principal maximal ideal and nonvanishing
generator powers is a DVR. Nonvanishing is proved for a principal completion
of a domain, without assuming the original domain is Noetherian or local.
Original proofs, no reference-engine code copied; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.SeparatedPrincipalLocalRing

noncomputable section
variable {R : Type*} [CommRing R]

theorem completion_pow_ne_zero [IsDomain R] (I : Ideal R) (π : R)
    (hI : I = Ideal.span {π}) (hπ : π ≠ 0) (hunit : ¬ IsUnit π) (n : ℕ) :
    (algebraMap R (AdicCompletion I R) π) ^ n ≠ 0 := by
  intro h
  have he := congrArg (AdicCompletion.evalₐ I (n + 1)) h
  have hm : π ^ n ∈ I ^ (n + 1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_pow, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Algebra.algebraMap_self, RingHom.id_apply, map_zero] using he
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨b, hb⟩ := hm
  have hone : 1 = π * b := by
    apply mul_left_cancel₀ (pow_ne_zero n hπ)
    simpa only [mul_one, pow_succ, mul_assoc] using hb
  exact hunit (isUnit_of_dvd_one ⟨b, hone⟩)

section Local
variable [IsLocalRing R] [IsHausdorff (IsLocalRing.maximalIdeal R) R]
variable (π : R) (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π})
include hspan

theorem exists_pow_not_dvd (x : R) (hx : x ≠ 0) : ∃ n : ℕ, ¬ π ^ n ∣ x := by
  by_contra! h
  apply hx
  apply IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal R) R) x
  intro n
  apply SModEq.zero.mpr
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top, hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    using h n

theorem factorization (x : R) (hx : x ≠ 0) : ∃ n : ℕ, ∃ u : Rˣ, x = π ^ n * u := by
  classical
  have ex := exists_pow_not_dvd π hspan x hx
  have hzero : Nat.find ex ≠ 0 := by
    intro h
    have hh := Nat.find_spec ex
    simp only [h, pow_zero, one_dvd, not_true_eq_false] at hh
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hdiv : π ^ n ∣ x := by
    by_contra h
    exact Nat.find_min ex (by omega) h
  have hnext : ¬ π ^ (n + 1) ∣ x := by
    simpa only [hn] using Nat.find_spec ex
  obtain ⟨b, hb⟩ := hdiv
  have hbu : IsUnit b := by
    by_contra h
    have hbm : b ∈ IsLocalRing.maximalIdeal R := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h
    rw [hspan, Ideal.mem_span_singleton] at hbm
    obtain ⟨c, hc⟩ := hbm
    apply hnext
    refine ⟨c, ?_⟩
    rw [hb, hc, pow_succ, mul_assoc]
  obtain ⟨u, hu⟩ := hbu
  exact ⟨n, u, by simpa only [hu] using hb⟩

theorem domain (hpow : ∀ n : ℕ, π ^ n ≠ 0) : IsDomain R := by
  apply (isDomain_iff_noZeroDivisors_and_nontrivial R).mpr
  refine ⟨⟨?_⟩, inferInstance⟩
  intro a b hab
  by_cases ha : a = 0
  · exact Or.inl ha
  by_cases hb : b = 0
  · exact Or.inr hb
  obtain ⟨m, u, hu⟩ := factorization π hspan a ha
  obtain ⟨n, v, hv⟩ := factorization π hspan b hb
  have h : π ^ (m + n) * ↑(u * v) = 0 := by
    simpa only [hu, hv, pow_add, Units.val_mul, mul_assoc, mul_left_comm, mul_comm] using hab
  exact False.elim (hpow (m + n) ((u * v).mul_left_eq_zero.mp h))

theorem discreteValuationRing (hpow : ∀ n : ℕ, π ^ n ≠ 0) :
    letI := domain π hspan hpow
    IsDiscreteValuationRing R := by
  let := domain π hspan hpow
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  have hπ : π ≠ 0 := by simpa only [pow_one] using hpow 1
  refine ⟨π, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ hspan, ?_⟩
  intro x hx
  obtain ⟨n, u, hu⟩ := factorization π hspan x hx
  exact ⟨n, u, hu.symm⟩

end Local
end
end JoshiTeich.Act1Scene1.SeparatedPrincipalLocalRing
