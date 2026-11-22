import Solutions.Source_ReferenceIutCor312PadicGaloisCore

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic

noncomputable section

attribute [local instance] LocalCompletion.selectedPrime LocalCompletion.completionNontrivialNorm
  LocalCompletion.completionComplete LocalCompletion.completionUltrametric

variable {K : Type*} [Field K] [NumberField K] (s : FinitePlace K)

local notation "Eₛ" => LocalCompletion.completionAt K s
local notation "Ωₛ" => AlgebraicClosure Eₛ
local notation "Ĉₛ" => CompletedAlgebraicClosure.Field Eₛ
local notation "eₛ" => LocalCompletion.completedPadicEquiv s

local notation "Cₛ" => PadicComplex (residueChar s)

private theorem conjugation_norm {A B : Type*} [NormedField A] [NormedField B]
    (e : A ≃+* B) (g : A ≃+* A) (g' : B ≃+* B) (d : ℕ) (hd : d ≠ 0)
    (hcomm : ∀ x, g' (e x) = e (g x)) (hpower : ∀ x, ‖e x‖ ^ d = ‖x‖)
    (hgnorm : ∀ x, ‖g x‖ = ‖x‖) (y : B) :
    ‖g' y‖ = ‖y‖ := by
  obtain ⟨x, rfl⟩ := e.surjective y
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd).mp
  rw [hcomm, hpower, hpower, hgnorm]

theorem padicComplexGalois_norm (σ : Ωₛ ≃ₐ[Eₛ] Ωₛ) (x : Cₛ) :
    ‖padicComplexGalois s σ x‖ = ‖x‖ :=
  conjugation_norm eₛ (CompletedAlgebraicClosure.extendGalois (K := Eₛ) σ)
    (padicComplexGalois s σ) (localDeg s) (localDeg_pos s).ne'
    (padicComplexGalois_completedPadicEquiv s σ) (LocalCompletion.completedPadicEquiv_norm_pow s)
    (CompletedAlgebraicClosure.extendGalois_norm (K := Eₛ) σ) x

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
