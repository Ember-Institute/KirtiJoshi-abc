import Solutions.Source_ReferenceIutCor312CrystallineGaloisComparison
import Solutions.Source_ReferenceIutCor312PadicGaloisNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicTiltField

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic
open CrystallineEnvelope

noncomputable section

attribute [local instance] LocalCompletion.selectedPrime LocalCompletion.completionNontrivialNorm
  LocalCompletion.completionComplete LocalCompletion.completionUltrametric

variable {K : Type*} [Field K] [NumberField K] (s : FinitePlace K)

local notation "pₛ" => residueChar s
local notation "Eₛ" => LocalCompletion.completionAt K s
local notation "Ωₛ" => AlgebraicClosure Eₛ
local notation "Ĉₛ" => CompletedAlgebraicClosure.Field Eₛ
local notation "Cₛ" => PadicComplex pₛ
local notation "eₛ" => LocalCompletion.completedPadicEquiv s

local instance completedPadicPrimeNorm : Fact (0 < ‖(pₛ : Ĉₛ)‖ ∧ ‖(pₛ : Ĉₛ)‖ < 1) := by
  have h := LocalCompletion.completedPadicEquiv_norm_pow s (pₛ : Ĉₛ)
  rw [map_natCast] at h
  have hp := (PadicTiltField.primeNormFact pₛ).out
  constructor
  rw [← h]
  exact ⟨pow_pos hp.1 _, pow_lt_one₀ hp.1.le hp.2 (localDeg_pos s).ne'⟩

/-- Compare the crystalline completions at the same finite place. -/
def completedPadicCrystallineEquiv : ACris Ĉₛ pₛ ≃+* ACris Cₛ pₛ :=
  equivACris pₛ eₛ (localDeg s) (localDeg_pos s)
    (LocalCompletion.completedPadicEquiv_norm_pow s)

private theorem padicComplexGalois_norm_pow_one (σ : Ωₛ ≃ₐ[Eₛ] Ωₛ) (x : Cₛ) :
    ‖padicComplexGalois s σ x‖ ^ (1 : ℕ) = ‖x‖ := by
  rw [pow_one, padicComplexGalois_norm]

/-- The original local Galois action induces this automorphism on standard `A_cris`. -/
def padicCrystallineGalois (σ : Ωₛ ≃ₐ[Eₛ] Ωₛ) : ACris Cₛ pₛ ≃+* ACris Cₛ pₛ :=
  equivACris pₛ (padicComplexGalois s σ) 1 Nat.one_pos
    (padicComplexGalois_norm_pow_one s σ)

theorem completedPadicCrystallineEquiv_extendGaloisACris
    (σ : Ωₛ ≃ₐ[Eₛ] Ωₛ) (z : ACris Ĉₛ pₛ) :
    completedPadicCrystallineEquiv s (CompletedAlgebraicClosure.extendGaloisACris pₛ σ z) =
      padicCrystallineGalois s σ (completedPadicCrystallineEquiv s z) :=
  CompletedAlgebraicClosure.equivACris_extendGaloisACris pₛ eₛ (localDeg s) (localDeg_pos s)
    (LocalCompletion.completedPadicEquiv_norm_pow s) σ (padicComplexGalois s σ)
    (padicComplexGalois_norm_pow_one s σ)
    (fun x => (padicComplexGalois_completedPadicEquiv s σ x).symm) z

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
