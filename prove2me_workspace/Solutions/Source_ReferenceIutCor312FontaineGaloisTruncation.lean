import Solutions.Source_ReferenceIutCor312FontaineGaloisResidues
import Mathlib.RingTheory.WittVector.Truncated
import Mathlib.Order.Filter.Finite

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open Filter JoshiTeich.Prologue
open scoped Topology

noncomputable section

private theorem isLocallyConstant_wittTruncate_map
    {X S R : Type*} [TopologicalSpace X] [CommRing S] [CommRing R]
    (p : ℕ) [Fact p.Prime] (k : ℕ) (f : S →+* R) (v : X → WittVector p S)
    (h : ∀ i : Fin k, IsLocallyConstant (fun x => f ((v x).coeff i))) :
    IsLocallyConstant (fun x => WittVector.truncate k (WittVector.map f (v x))) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have h' : ∀ᶠ y in 𝓝 x, ∀ i : Fin k, f ((v y).coeff i) = f ((v x).coeff i) :=
    Filter.eventually_all.mpr fun i => (h i).eventually_eq x
  filter_upwards [h'] with y hy
  apply TruncatedWittVector.ext
  intro i
  simpa only [WittVector.coeff_truncate, WittVector.map_coeff] using hy i

variable {K : Type*} [hK : NontriviallyNormedField K] [hComplete : CompleteSpace K]
  [hUltra : IsUltrametricDist K]
variable (p : ℕ) [hpPrime : Fact p.Prime]
variable [hpNorm : Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω" => Algebraic K
local notation "C" => Field K
local notation "G" => (Ω ≃ₐ[K] Ω)
local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "𝒯" => PreTilt 𝒪 p
local notation "𝔸" => WittVector p 𝒯
local notation "reduceCoeff" => (@PreTilt.coeff 𝒪 _ p hpPrime
  (LocalGeometricFontaine.primeNonunitFact C p))

/-- Truncate a Fontaine Witt vector after applying a fixed pretilt projection. -/
def fontaineTruncatedReduction (k n : ℕ) : 𝔸 →+* TruncatedWittVector p k (ModP 𝒪 p) :=
  (WittVector.truncate (p := p) (R := ModP 𝒪 p) k).comp
    (WittVector.map (reduceCoeff n))

theorem fontaineTruncatedReduction_coeff (k n : ℕ) (w : 𝔸) (i : Fin k) :
    (fontaineTruncatedReduction (K := K) p k n w).coeff i = reduceCoeff n (w.coeff i) :=
  rfl

/-- The orbit of each finite truncation of a fixed Witt vector after
applying a fixed pretilt projection is locally constant for the Krull topology. -/
theorem fontaineTruncatedReduction_extendGalois_isLocallyConstant (w : 𝔸) (k n : ℕ) :
    IsLocallyConstant (fun σ : G =>
      fontaineTruncatedReduction (K := K) p k n
        ((@extendGaloisFontaine K hK hComplete hUltra p hpPrime hpNorm σ) w)) := by
  let orbit : G → 𝔸 := fun σ =>
    (@extendGaloisFontaine K hK hComplete hUltra p hpPrime hpNorm σ) w
  exact isLocallyConstant_wittTruncate_map p k (reduceCoeff n) orbit
    (fun i => preTiltCoeff_extendGaloisFontaine_isLocallyConstant (K := K) p w i n)

/-- The difference between orbit values has zero reduced truncation
in a Krull neighborhood of each group element. -/
theorem fontaineTruncatedReduction_extendGalois_sub_eventually_eq_zero
    (w : 𝔸) (k n : ℕ) (σ : G) :
    ∀ᶠ τ : G in 𝓝 σ, fontaineTruncatedReduction (K := K) p k n
      ((@extendGaloisFontaine K hK hComplete hUltra p hpPrime hpNorm τ) w -
        (@extendGaloisFontaine K hK hComplete hUltra p hpPrime hpNorm σ) w) = 0 := by
  let f := fontaineTruncatedReduction (K := K) p k n
  filter_upwards [(fontaineTruncatedReduction_extendGalois_isLocallyConstant p w k n).eventually_eq σ]
    with τ hτ
  exact (map_sub f _ _).trans (sub_eq_zero.mpr hτ)

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
