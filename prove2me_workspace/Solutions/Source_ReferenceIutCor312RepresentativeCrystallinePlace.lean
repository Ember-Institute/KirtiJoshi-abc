import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineUnit
import Solutions.Source_ReferenceIutCor312PadicKummerCrystallineBridge

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic

universe u v

noncomputable section

local instance representativeCrystallinePlacePrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : Fact (residueChar s).Prime :=
  LocalCompletion.selectedPrime s

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt)

local notation "pₛ" => residueChar s
local notation "Eₛ" => LocalCompletion.completionAt D.Kt s
local notation "Ωₛ" => AlgebraicClosure Eₛ

private def paperQRootLogInput :
    {x : CrystallineEnvelope.PadicPreTilt pₛ // CrystallineEnvelope.isPadicLogInput pₛ x} :=
  CrystallineEnvelope.padicKummerLogInput (K := Eₛ) (Ω := Ωₛ) pₛ
    (TL.paperQRootKummerRootTower s) (algebraicClosureInPadicComplex s)
    (TL.paperQRootPrincipalUnit_crystalline_inputs s).1
    (TL.paperQRootPrincipalUnit_crystalline_inputs s).2

/-- The original Kummer tower gives a pretilt element over standard `ℂ_p`. -/
abbrev paperQRootKummerPreTilt : CrystallineEnvelope.PadicPreTilt pₛ :=
  (paperQRootLogInput TL s).1

/-- The Kummer numerator starts in the sum of the Fontaine kernel and the prime ideal. -/
theorem paperQRootKummerPreTilt_teichmuller_sub_one_mem_theta_ker_sup_prime :
    CrystallineEnvelope.isPadicLogInput pₛ (TL.paperQRootKummerPreTilt s) :=
  (paperQRootLogInput TL s).2

/-- The logarithm of the original Kummer tower in the integral crystalline completion. -/
def paperQRootCrystallineLog : CrystallineEnvelope.PadicACris pₛ :=
  CrystallineEnvelope.padicKummerLog (K := Eₛ) (Ω := Ωₛ) pₛ
    (TL.paperQRootKummerRootTower s)
    (algebraicClosureInPadicComplex s) (TL.paperQRootPrincipalUnit_crystalline_inputs s).1
    (TL.paperQRootPrincipalUnit_crystalline_inputs s).2

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
