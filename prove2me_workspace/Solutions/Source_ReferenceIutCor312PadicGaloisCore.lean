import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraicPadicNorm
import Solutions.Source_ReferenceIutCor312CompletedGalois

/-!
Transport the completed local action from Joshi III, §9.6, to standard `ℂ_p`.
-/

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

/-- Conjugate the completed action by the actual local comparison with standard `ℂ_p`. -/
def padicComplexGalois (σ : Ωₛ ≃ₐ[Eₛ] Ωₛ) : Cₛ ≃+* Cₛ :=
  (RingEquiv.trans (RingEquiv.symm eₛ)
    (CompletedAlgebraicClosure.extendGalois (K := Eₛ) σ)).trans eₛ

theorem padicComplexGalois_completedPadicEquiv
    (σ : Ωₛ ≃ₐ[Eₛ] Ωₛ) (x : Ĉₛ) :
    padicComplexGalois s σ (eₛ x) =
      eₛ (CompletedAlgebraicClosure.extendGalois (K := Eₛ) σ x) :=
  congrArg (fun y : Ĉₛ => eₛ (CompletedAlgebraicClosure.extendGalois (K := Eₛ) σ y))
    (RingEquiv.symm_apply_apply eₛ x)

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
