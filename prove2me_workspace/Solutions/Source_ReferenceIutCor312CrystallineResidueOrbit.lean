import Solutions.Source_ReferenceIutCor312CrystallineA0Orbit

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open CrystallineEnvelope

noncomputable section

private theorem mk_prime_pow_eq_of_dvd_sub {R : Type*} [CommRing R]
    (p k : ℕ) (x y : R) (h : (p : R) ^ k ∣ x - y) :
    Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ k) x =
      Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ k) y := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := (Ideal.span {(p : R)}) ^ k) x y).mpr
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact h

variable {K : Type*} [hK : NontriviallyNormedField K] [hComplete : CompleteSpace K]
  [hUltra : IsUltrametricDist K] [CharZero K]
variable (p : ℕ) [hpPrime : Fact p.Prime]
variable [hpNorm : Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "C" => Field K
local notation "G" => (Algebraic K ≃ₐ[K] Algebraic K)
local notation "D" => A0 C p
local notation "A" => ACris C p
local notation "I" => (Ideal.span {(p : D)})
local notation "galoisA0" => @extendGaloisA0 K hK hComplete hUltra p hpPrime hpNorm
local notation "galoisACris" => @extendGaloisACris K hK hComplete hUltra p hpPrime hpNorm

/-- For a fixed element of the crystalline completion, its Galois orbit
projected to any prime-power quotient is locally constant. -/
theorem eval_extendGaloisACris_isLocallyConstant (k : ℕ) (z : A) :
    IsLocallyConstant (fun σ : G => AdicCompletion.evalₐ I k (galoisACris σ z)) := by
  let eval := AdicCompletion.evalₐ I k
  let q : D →+* D ⧸ I ^ k := Ideal.Quotient.mk (I ^ k)
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (eval z)
  have horbit (σ : G) : eval (galoisACris σ z) = q (galoisA0 σ w) :=
    eval_mapACris_of_eq C p (galoisA0 σ) k z w hw.symm
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro σ
  filter_upwards [extendGaloisA0_sub_prime_pow_dvd_eventually p w k σ] with τ hτ
  exact (horbit τ).trans
    ((mk_prime_pow_eq_of_dvd_sub p k (galoisA0 τ w) (galoisA0 σ w) hτ).trans (horbit σ).symm)

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
