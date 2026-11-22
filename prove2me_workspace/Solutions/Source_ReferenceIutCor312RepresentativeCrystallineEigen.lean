import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineValue
import Solutions.Source_ReferenceIutCor312PadicCrystallineEigen

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic
open CrystallineEnvelope

universe u v

noncomputable section

local instance representativeCrystallineEigenPrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : Fact (residueChar s).Prime :=
  LocalCompletion.selectedPrime s

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT)

section FinitePlace

variable (s : FinitePlace D.Kt)

local notation "pₛ" => residueChar s
local notation "Eₛ" => LocalCompletion.completionAt D.Kt s
local notation "Ωₛ" => AlgebraicClosure Eₛ
local notation "aₛ" => ((TL.paperQRootPrincipalUnit s).1 : Eₛ)

private theorem frobenius_paperQRootCrystallineLog :
    isPadicFrobeniusPrimeEigen pₛ (TL.paperQRootCrystallineLog s) := by
  have h := isPadicFrobeniusPrimeEigen_padicKummerLog
    (K := Eₛ) (Ω := Ωₛ) (a := aₛ) pₛ
    (TL.paperQRootKummerRootTower s) (algebraicClosureInPadicComplex s)
    (TL.paperQRootPrincipalUnit_crystalline_inputs s).1
    (TL.paperQRootPrincipalUnit_crystalline_inputs s).2
  exact Eq.mpr
    (congrArg (isPadicFrobeniusPrimeEigen pₛ) (TL.paperQRootCrystallineLog_eq_padicKummerLog s)) h

end FinitePlace

variable (QI : QPilotInputs D) (w : QI.badModuliFinset)

local notation "s₀" => D.localData.sect.sectFin (Subtype.val w)
local notation "p₀" => residueChar s₀

/-- The P7 section logarithm lies in the Frobenius p-eigenspace. -/
theorem frobenius_sectionPaperQRootCrystallineLog :
    isPadicFrobeniusPrimeEigen p₀ (sectionPaperQRootCrystallineLog TL QI w) := by
  have hValue := sectionPaperQRootCrystallineLog_eq_paperQRootCrystallineLog TL QI w
  exact Eq.mpr (congrArg (isPadicFrobeniusPrimeEigen p₀) hValue)
    (frobenius_paperQRootCrystallineLog TL s₀)

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
