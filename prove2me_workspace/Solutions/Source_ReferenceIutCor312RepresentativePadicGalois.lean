import Solutions.Source_ReferenceIutCor312PadicGaloisCore
import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineCompletion

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

/-- The standard action extends the original automorphisms on the Kummer coordinates. -/
theorem padicComplexGalois_algebraicClosureInPadicComplex
    (σ : Ωₛ ≃ₐ[Eₛ] Ωₛ) (x : Ωₛ) :
    padicComplexGalois s σ (algebraicClosureInPadicComplex s x) =
      algebraicClosureInPadicComplex s (σ x) := by
  let a : LocalCompletion.AlgebraicCompletion s := x
  let b : LocalCompletion.AlgebraicCompletion s := σ x
  have hEmbed : eₛ (a : Ĉₛ) = algebraicClosureInPadicComplex s x :=
    LocalCompletion.completedPadicEquiv_coe s a
  have hEmbedImage : eₛ (b : Ĉₛ) = algebraicClosureInPadicComplex s (σ x) :=
    LocalCompletion.completedPadicEquiv_coe s b
  have hAction : CompletedAlgebraicClosure.extendGalois (K := Eₛ) σ (a : Ĉₛ) =
      (b : Ĉₛ) := CompletedAlgebraicClosure.extendGalois_coe (K := Eₛ) σ a
  exact (congrArg (padicComplexGalois s σ) hEmbed.symm).trans
    ((padicComplexGalois_completedPadicEquiv s σ (a : Ĉₛ)).trans
      ((congrArg eₛ hAction).trans hEmbedImage))

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
