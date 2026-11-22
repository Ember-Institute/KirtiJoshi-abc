import Solutions.Source_ReferenceIutCor312FinitePlaceCrystallineLogComparison
import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineInputs

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic
open CrystallineEnvelope

universe u v

noncomputable section

attribute [local instance] LocalCompletion.completionNontrivialNorm
  LocalCompletion.completionComplete LocalCompletion.completionUltrametric
  finitePlaceCrystallinePrime finitePlaceCrystallinePrimeNorm

local notation "p[" s "]" => JoshiTeich.Prologue.Arithmetic.residueChar s
local notation "E[" s "]" => LocalCompletion.completionAt _ s
local notation "Ω[" s "]" => AlgebraicClosure E[s]
local notation "C[" s "]" => PadicComplex p[s]

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

/-- The original P7 root tower gives the completed Kummer logarithm at this place. -/
def completedPaperQRootCrystallineLog (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    ACris (CompletedAlgebraicClosure.Field E[s]) p[s] :=
  finitePlaceCompletedKummerLog s
    (paperQRootPrincipalUnit_crystalline_inputs TL s).1
    (paperQRootPrincipalUnit_crystalline_inputs TL s).2
    (paperQRootKummerRootTower TL s)

theorem completedPadicCrystallineEquiv_paperQRootCrystallineLog
    (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    completedPadicCrystallineEquiv s (completedPaperQRootCrystallineLog TL s) =
      (paperQRootCrystallineLog TL s : ACris C[s] p[s]) :=
  completedPadicCrystallineEquiv_finitePlaceCompletedKummerLog s (paperQRootKummerRootTower TL s)
    (paperQRootPrincipalUnit_crystalline_inputs TL s).1
    (paperQRootPrincipalUnit_crystalline_inputs TL s).2

/-- The standard crystalline Galois difference uses the cocycle of the original P7 tower. -/
theorem padicCrystallineGalois_paperQRootCrystallineLog_sub
    (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) (σ : Ω[s] ≃ₐ[E[s] ] Ω[s]) :
    let value : ACris C[s] p[s] := paperQRootCrystallineLog TL s
    padicCrystallineGalois s σ value - value =
      cyclotomicLog C[s] p[s]
        (LocalKummer.RootTower.mapKummerCocycle (paperQRootKummerRootTower TL s)
          (algebraicClosureInPadicComplex s)
          (Units.ne_zero (Subtype.val (paperQRootPrincipalUnit TL s))) σ) :=
  padicCrystallineGalois_finitePlaceKummerLog_sub s (paperQRootKummerRootTower TL s)
    (paperQRootPrincipalUnit_crystalline_inputs TL s).1
    (paperQRootPrincipalUnit_crystalline_inputs TL s).2
    (Units.ne_zero (Subtype.val (paperQRootPrincipalUnit TL s))) σ

/-- The Galois difference formula at the representative selected by the P7 section. -/
theorem padicCrystallineGalois_sectionPaperQRootCrystallineLog_sub
    (TL : ThetaLocalData D LT) (QI : QPilotInputs D) (w : QI.badModuliFinset) :
    let s := D.localData.sect.sectFin (Subtype.val w)
    ∀ σ : Ω[s] ≃ₐ[E[s] ] Ω[s],
      let value : ACris C[s] p[s] := sectionPaperQRootCrystallineLog TL QI w
      padicCrystallineGalois s σ value - value =
        cyclotomicLog C[s] p[s]
          (LocalKummer.RootTower.mapKummerCocycle (paperQRootKummerRootTower TL s)
            (algebraicClosureInPadicComplex s)
            (Units.ne_zero (Subtype.val (paperQRootPrincipalUnit TL s))) σ) :=
  padicCrystallineGalois_paperQRootCrystallineLog_sub TL (D.localData.sect.sectFin (Subtype.val w))

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
