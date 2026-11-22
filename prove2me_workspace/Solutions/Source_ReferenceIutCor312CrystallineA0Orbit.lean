import Solutions.Source_ReferenceIutCor312CrystallineFontaineOrbit
import Solutions.Source_ReferenceIutCor312CrystallineGalois

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope
open scoped Topology

noncomputable section

private theorem dvd_of_dvd_mul_pow_of_unit_image {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (c x : R) (hc : IsUnit (f c))
    (k d : ℕ) (h : c ^ (k + d) ∣ x * c ^ d) : c ^ k ∣ x := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, hf ((hc.pow d).mul_right_cancel ?_)⟩
  calc
    f x * f c ^ d = f (x * c ^ d) := by rw [map_mul, map_pow]
    _ = f (c ^ (k + d) * v) := congrArg f hv
    _ = f (c ^ k * v) * f c ^ d := by
      simp only [map_mul, map_pow, pow_add]
      ac_rfl

private theorem sub_map_mul_natCast_pow {R : Type*} [CommRing R]
    (f g : R →+* R) (z : R) (n d : ℕ) :
    (f z - g z) * (n : R) ^ d = f (z * (n : R) ^ d) - g (z * (n : R) ^ d) := by
  simp only [map_mul, map_pow, map_natCast, sub_mul]

variable {K : Type*} [hK : NontriviallyNormedField K] [hComplete : CompleteSpace K]
  [hUltra : IsUltrametricDist K] [CharZero K]
variable (p : ℕ) [hpPrime : Fact p.Prime]
variable [hpNorm : Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "C" => Field K
local notation "G" => (Algebraic K ≃ₐ[K] Algebraic K)
local notation "W" => Ainf C p
local notation "B" => AinfInvertP C p
local notation "D" => A0 C p
local notation "ι" => algebraMap W D
local notation "galoisWitt" => @extendGaloisFontaine K hK hComplete hUltra p hpPrime hpNorm
local notation "galoisA0" => @extendGaloisA0 K hK hComplete hUltra p hpPrime hpNorm

private theorem A0_exists_mul_prime_pow_eq (z : D) :
    ∃ (w : W) (d : ℕ), z * (p : D) ^ d = ι w := by
  obtain ⟨⟨w, b⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (p : W)) (z : B)
  obtain ⟨d, hd⟩ := b.property
  have hpow : (p : D) ^ d = ι (b : W) := by rw [← hd, map_pow, map_natCast]
  have hclear : z * ι (b : W) = ι w := by
    apply Subtype.ext
    exact hb
  exact ⟨w, d, (congrArg (fun q : D => z * q) hpow).trans hclear⟩

private theorem extendGaloisA0_sub_mul_prime_pow_eq
    (z : D) (w : W) (d : ℕ) (hclear : z * (p : D) ^ d = ι w) (σ τ : G) :
    (galoisA0 τ z - galoisA0 σ z) * (p : D) ^ d =
      ι (galoisWitt τ w - galoisWitt σ w) := by
  have hτ : galoisA0 τ (z * (p : D) ^ d) = ι (galoisWitt τ w) :=
    (congrArg (galoisA0 τ) hclear).trans (extendGaloisA0_algebraMap p τ w)
  have hσ : galoisA0 σ (z * (p : D) ^ d) = ι (galoisWitt σ w) :=
    (congrArg (galoisA0 σ) hclear).trans (extendGaloisA0_algebraMap p σ w)
  exact (sub_map_mul_natCast_pow (galoisA0 τ) (galoisA0 σ) z p d).trans
    ((congrArg₂ (fun x y : D => x - y) hτ hσ).trans (map_sub ι _ _).symm)

/-- The difference between two nearby Galois orbit values in the
divided-power ring is divisible by the prescribed prime power. -/
theorem extendGaloisA0_sub_prime_pow_dvd_eventually (z : D) (k : ℕ) (σ : G) :
    ∀ᶠ τ : G in 𝓝 σ, (p : D) ^ k ∣ galoisA0 τ z - galoisA0 σ z := by
  obtain ⟨w, d, hclear⟩ := A0_exists_mul_prime_pow_eq p z
  let f : D →+* B := (A0 C p).val.toRingHom
  have hunit : IsUnit (f (p : D)) :=
    (map_natCast f p).symm ▸ natCast_isUnit C p p hpPrime.out.ne_zero
  filter_upwards [extendGaloisFontaine_sub_prime_pow_dvd_eventually p w (k + d) σ] with τ hτ
  apply dvd_of_dvd_mul_pow_of_unit_image f (fun _ _ h => Subtype.ext h)
    (p : D) (galoisA0 τ z - galoisA0 σ z) hunit k d
  exact (extendGaloisA0_sub_mul_prime_pow_eq p z w d hclear σ τ).symm ▸ hτ

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
