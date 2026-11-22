import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineInputs

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic
open CrystallineEnvelope

universe u v

noncomputable section

local instance representativeCrystallineValuePrime {K : Type*} [Field K] [NumberField K]
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

/-- The representative value is the standard crystalline logarithm of the same root tower. -/
theorem paperQRootCrystallineLog_eq_padicKummerLog :
    TL.paperQRootCrystallineLog s =
      padicKummerLog (K := Eₛ) (Ω := Ωₛ) (a := (TL.paperQRootPrincipalUnit s).1) pₛ
        (TL.paperQRootKummerRootTower s) (algebraicClosureInPadicComplex s)
        (TL.paperQRootPrincipalUnit_crystalline_inputs s).1
        (TL.paperQRootPrincipalUnit_crystalline_inputs s).2 := rfl

end FinitePlace

/-- The section uses the value at its chosen representative. -/
theorem sectionPaperQRootCrystallineLog_eq_paperQRootCrystallineLog
    (QI : QPilotInputs D) (w : QI.badModuliFinset) :
    sectionPaperQRootCrystallineLog TL QI w =
      TL.paperQRootCrystallineLog (D.localData.sect.sectFin w.1) := rfl

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
