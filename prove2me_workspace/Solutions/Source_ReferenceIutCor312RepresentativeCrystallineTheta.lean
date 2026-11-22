import Solutions.Source_ReferenceIutCor312PadicKummerCrystallineTheta
import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineValue

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic
open CrystallineEnvelope
open scoped Valued

universe u v

noncomputable section

local instance representativeCrystallineThetaPrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : Fact (residueChar s).Prime :=
  LocalCompletion.selectedPrime s

local instance representativeCrystallineThetaCharZero {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : CharZero (LocalCompletion.completionAt K s) :=
  LocalCompletion.completionCharZero s

private theorem continuous_completionInPadicComplex_ringHom
    {K : Type*} [Field K] [NumberField K] (s : FinitePlace K) :
    Continuous ((algebraicClosureInPadicComplex s).comp
      (algebraMap (LocalCompletion.completionAt K s)
        (AlgebraicClosure (LocalCompletion.completionAt K s)))) := by
  let E := LocalCompletion.completionAt K s
  let j : E →+* PadicComplex (residueChar s) :=
    (algebraicClosureInPadicComplex s).comp (algebraMap E (AlgebraicClosure E))
  change Continuous j
  apply Metric.continuous_iff.mpr
  intro x ε hε
  refine ⟨ε ^ localDeg s, pow_pos hε _, fun y hy => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  apply lt_of_pow_lt_pow_left₀ (localDeg s) hε.le
  change ‖algebraicClosureInPadicComplex s (algebraMap E (AlgebraicClosure E) (y - x))‖ ^
    localDeg s < ε ^ localDeg s
  rw [algebraicClosureInPadicComplex_algebraMap, completionInPadicComplex_norm_pow]
  simpa only [dist_eq_norm] using hy

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT)

section FinitePlace

variable (s : FinitePlace D.Kt)

local notation "pₛ" => residueChar s
local notation "Cₛ" => PadicComplex pₛ
local notation "Eₛ" => LocalCompletion.completionAt D.Kt s
local notation "Ωₛ" => AlgebraicClosure Eₛ
local notation "aₛ" => ((TL.paperQRootPrincipalUnit s).1 : Eₛ)
local notation "Jₛ" => LocalCompletion.KummerValuation.ambientLog s pₛ rfl
  (TL.paperQRootKummerClass s)

private theorem paperQRootPadicLog_image :
    algebraicClosureInPadicComplex s (algebraMap Eₛ Ωₛ (LocalPadicLog.padicLog aₛ)) =
      completionInPadicComplex s Jₛ :=
  (algebraicClosureInPadicComplex_algebraMap s (LocalPadicLog.padicLog aₛ)).trans
    (congrArg (completionInPadicComplex s) (TL.ambientLog_paperQRootKummerClass s).symm)

/-- The crystalline numerator specializes to the ambient logarithm of the original Kummer class. -/
theorem thetaCrystalline_paperQRootCrystallineLog :
    isPadicThetaValue pₛ (TL.paperQRootCrystallineLog s) (completionInPadicComplex s Jₛ) := by
  have hpk : ‖(pₛ : Eₛ)‖ < 1 :=
    LocalCompletion.KummerValuation.prime_norm_lt_one s pₛ rfl
  have hprincipal : ‖aₛ - 1‖ < 1 := (TL.paperQRootPrincipalUnit s).2
  have h := isPadicThetaValue_padicKummerLog (k := Eₛ) (Ω := Ωₛ) (u := aₛ) pₛ
    (TL.paperQRootKummerRootTower s) (algebraicClosureInPadicComplex s)
    (continuous_completionInPadicComplex_ringHom s)
    (TL.paperQRootPrincipalUnit_crystalline_inputs s).1
    (TL.paperQRootPrincipalUnit_crystalline_inputs s).2 hpk hprincipal
  exact Eq.mp (congrArg₂ (isPadicThetaValue pₛ)
    (TL.paperQRootCrystallineLog_eq_padicKummerLog s).symm (paperQRootPadicLog_image TL s)) h

end FinitePlace

variable (QI : QPilotInputs D) (w : QI.badModuliFinset)

local notation "s₀" => D.localData.sect.sectFin (Subtype.val w)
local notation "p₀" => residueChar s₀
local notation "J₀" => LocalCompletion.KummerValuation.ambientLog s₀ p₀ rfl
  (TL.paperQRootKummerClass s₀)

/-- The Fontaine image of the numerator at the representative that the P7 section selects. -/
theorem thetaCrystalline_sectionPaperQRootCrystallineLog :
    isPadicThetaValue p₀ (sectionPaperQRootCrystallineLog TL QI w)
      (completionInPadicComplex s₀ J₀) := by
  let P : PadicACris p₀ → Prop := fun x =>
    isPadicThetaValue p₀ x (completionInPadicComplex s₀ J₀)
  exact Eq.mpr
    (congrArg P (sectionPaperQRootCrystallineLog_eq_paperQRootCrystallineLog TL QI w))
    (thetaCrystalline_paperQRootCrystallineLog TL s₀)

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
