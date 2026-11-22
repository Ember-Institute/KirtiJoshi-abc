import Solutions.Source_ReferenceIutCor312FontaineGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerContinuity

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue

noncomputable section

variable {K : Type*} [hK : NontriviallyNormedField K]
  [hComplete : CompleteSpace K] [hUltra : IsUltrametricDist K]
variable (p : ℕ)

local notation "Ω" => Algebraic K
local notation "C" => Field K
local notation "G" => (Ω ≃ₐ[K] Ω)
local notation "𝒪" => LocalGeometricFontaine.integerRing C

/-- The Galois orbit of a residue of the completed valuation ring is locally constant. -/
theorem extendGaloisModP_isLocallyConstant (hp : 0 < ‖(p : C)‖) (x : ModP 𝒪 p) :
    IsLocallyConstant (fun σ : G => extendGaloisModP p σ x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro σ
  have hdense : DenseRange (fun a : Ω => (a : C)) := UniformSpace.Completion.denseRange_coe
  obtain ⟨a, ha⟩ := hdense.exists_dist_lt (x : C) hp
  have ha_loc := (LocalKummer.galoisEval_isLocallyConstant (K := K) a).eventually_eq σ
  filter_upwards [ha_loc] with τ hτ
  have hfix : extendGalois τ (a : C) = extendGalois σ (a : C) := by
    rw [extendGalois_coe, extendGalois_coe, hτ]
  have hdist (γ : G) : dist (extendGalois γ (x : C)) (extendGalois γ (a : C)) =
      dist (x : C) (a : C) := by
    simp only [dist_eq_norm, ← map_sub, extendGalois_norm]
  rw [extendGaloisModP_mk, extendGaloisModP_mk, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  change _ ∈ (Ideal.span {(p : 𝒪)} : Set 𝒪)
  rw [LocalGeometricFontaine.principalIdeal_eq_closedBall]
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, Subring.coe_natCast,
    AddSubgroupClass.coe_sub, extendGaloisIntegers_coe]
  rw [← dist_eq_norm]
  calc
    _ ≤ max (dist (extendGalois τ (x : C)) (extendGalois τ (a : C)))
        (dist (extendGalois τ (a : C)) (extendGalois σ (x : C))) :=
      IsUltrametricDist.dist_triangle_max _ _ _
    _ ≤ ‖(p : C)‖ := by
      rw [hdist τ, hfix, dist_comm (extendGalois σ (a : C)), hdist σ, max_self]
      exact ha.le

variable [hpPrime : Fact p.Prime]
variable [hpNorm : Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "𝒯" => PreTilt 𝒪 p
local notation "𝔸" => WittVector p 𝒯

private def wittResidueCoordinate (w : 𝔸) (i n : ℕ) : ModP 𝒪 p :=
  (show Perfection (ModP 𝒪 p) p from w.coeff i).val n

private local instance residue_prime_nonunit : Fact (¬ IsUnit (p : 𝒪)) :=
  LocalGeometricFontaine.primeNonunitFact (Field K) p

include hpPrime hpNorm

/-- Select one pretilt coordinate of one Witt digit in a Galois orbit. -/
def fontaineOrbitCoeff (w : 𝔸) (i n : ℕ) (σ : G) : ModP 𝒪 p := by
  let action : 𝔸 ≃+* 𝔸 := @extendGaloisFontaine K hK hComplete hUltra p hpPrime hpNorm σ
  let moved : 𝔸 := action w
  exact wittResidueCoordinate (K := K) p moved i n

private theorem fontaineOrbitCoeff_eq (w : 𝔸) (i n : ℕ) (σ : G) :
    fontaineOrbitCoeff (K := K) p w i n σ =
      extendGaloisModP (K := K) p σ (wittResidueCoordinate (K := K) p w i n) := by
  let project : 𝒯 → ModP 𝒪 p := fun x => (show Perfection (ModP 𝒪 p) p from x).val n
  have hWitt := @coeff_extendGaloisFontaine K hK hComplete hUltra p hpPrime hpNorm σ w i
  have hPreTilt := @coeff_extendGaloisPreTilt K hK hComplete hUltra p hpPrime hpNorm σ (w.coeff i) n
  exact (congrArg project hWitt).trans hPreTilt

/-- Each pretilt coordinate of a Witt digit of the Galois orbit is locally constant. -/
theorem preTiltCoeff_extendGaloisFontaine_isLocallyConstant
    (w : 𝔸) (i n : ℕ) :
    IsLocallyConstant (fontaineOrbitCoeff (K := K) p w i n) := by
  have h : fontaineOrbitCoeff (K := K) p w i n =
      (fun σ : G => extendGaloisModP (K := K) p σ (wittResidueCoordinate (K := K) p w i n)) :=
    funext (fontaineOrbitCoeff_eq (K := K) p w i n)
  rw [h]
  exact extendGaloisModP_isLocallyConstant (K := K) p hpNorm.out.1
    (wittResidueCoordinate (K := K) p w i n)

#check preTiltCoeff_extendGaloisFontaine_isLocallyConstant
#print axioms fontaineOrbitCoeff
#print axioms preTiltCoeff_extendGaloisFontaine_isLocallyConstant

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
