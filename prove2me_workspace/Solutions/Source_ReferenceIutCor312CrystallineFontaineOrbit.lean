import Solutions.Source_ReferenceIutCor312CrystallineTruncationDivisibility
import Solutions.Source_ReferenceIutCor312CrystallineTruncationFactor
import Solutions.Source_ReferenceIutCor312FontaineGaloisTruncation

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope
open scoped Topology

noncomputable section

variable {K : Type*} [hK : NontriviallyNormedField K] [hComplete : CompleteSpace K]
  [hUltra : IsUltrametricDist K] [CharZero K]
variable (p : ℕ) [hpPrime : Fact p.Prime]
variable [hpNorm : Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "C" => Field K
local notation "G" => (Algebraic K ≃ₐ[K] Algebraic K)
local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "W" => Ainf C p
local notation "D" => A0 C p
local notation "galoisWitt" => @extendGaloisFontaine K hK hComplete hUltra p hpPrime hpNorm

private theorem preTilt_coeff_eq_zero_of_truncation
    (w : W) (k n i : ℕ) (hi : i < k)
    (hw : fontaineTruncatedReduction (K := K) p k n w = 0) :
    PreTilt.coeff n (w.coeff i) = 0 := by
  let j : Fin k := ⟨i, hi⟩
  have h := congrArg (fun x : TruncatedWittVector p k (ModP 𝒪 p) => x.coeff j) hw
  exact (fontaineTruncatedReduction_coeff (K := K) p k n w j).symm.trans
    (h.trans (TruncatedWittVector.coeff_zero p k (ModP 𝒪 p) j))

/-- The difference between two nearby Galois orbit values of a Fontaine Witt
vector belongs to the prescribed prime-power ideal in the divided-power ring. -/
theorem extendGaloisFontaine_sub_prime_pow_dvd_eventually
    (w : W) (k : ℕ) (σ : G) :
    ∀ᶠ τ : G in 𝓝 σ, (p : D) ^ k ∣ algebraMap W D (galoisWitt τ w - galoisWitt σ w) := by
  cases k with
  | zero =>
      exact Filter.Eventually.of_forall fun τ => by
        rw [pow_zero]
        exact one_dvd _
  | succ k =>
      let m := p * (k + 1)
      let n := m * p ^ k
      have hdepth : m * p ^ k ≤ p ^ n :=
        (Nat.lt_two_pow_self : n < 2 ^ n).le.trans (Nat.pow_le_pow_left hpPrime.out.two_le n)
      filter_upwards
        [(fontaineTruncatedReduction_extendGalois_sub_eventually_eq_zero (K := K)
          p w (k + 1) n σ)] with τ hτ
      let d : W := galoisWitt τ w - galoisWitt σ w
      have hcoeff (i : ℕ) (hi : i ≤ k) : PreTilt.coeff n (d.coeff i) = 0 :=
        preTilt_coeff_eq_zero_of_truncation p d (k + 1) n i (Nat.lt_succ_iff.mpr hi) hτ
      obtain ⟨v, hv⟩ :=
        exists_primeTilt_teichmuller_multiple_of_coeff_zero C p d k n m hdepth hcoeff
      exact prime_pow_dvd_algebraMap_of_sub_pow_mul C p (k + 1)
        (WittVector.teichmuller p (primeTilt C p)) d v
        (teichmuller_primeTilt_mem_ker_sup_prime C p) hv

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
