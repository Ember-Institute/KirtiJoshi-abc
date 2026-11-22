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

private def conjugateAut {G A B : Type*} [Monoid G] [Add A] [Mul A] [Add B] [Mul B]
    (e : A ≃+* B) (ρ : G →* (A ≃+* A)) : G →* (B ≃+* B) where
  toFun σ := (e.symm.trans (ρ σ)).trans e
  map_one' := by
    apply RingEquiv.ext
    intro x
    simp only [RingEquiv.trans_apply, map_one, RingAut.one_apply, RingEquiv.apply_symm_apply]
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    simp only [RingAut.mul_apply, RingEquiv.trans_apply, map_mul, RingEquiv.symm_apply_apply]

/-- The conjugated automorphisms preserve the identity and composition. -/
def padicComplexGaloisAction : (Ωₛ ≃ₐ[Eₛ] Ωₛ) →* (Cₛ ≃+* Cₛ) :=
  conjugateAut eₛ (CompletedAlgebraicClosure.galoisCompletion (K := Eₛ))

theorem padicComplexGaloisAction_apply (σ : Ωₛ ≃ₐ[Eₛ] Ωₛ) :
    padicComplexGaloisAction s σ = padicComplexGalois s σ := rfl

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
