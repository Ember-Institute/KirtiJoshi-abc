import Solutions.Source_ReferenceIutCor312KummerCrystallineLogComparison
import Solutions.Source_ReferenceIutCor312KummerCrystallineCoboundary
import Solutions.Source_ReferenceIutCor312PadicKummerCrystallineBridge
import Solutions.Source_ReferenceIutCor312FinitePlaceCompletedKummerLog

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic
open CrystallineEnvelope GeometricTiltComparison

noncomputable section

attribute [local instance] LocalCompletion.completionNontrivialNorm
  LocalCompletion.completionComplete LocalCompletion.completionUltrametric

private local instance finitePlaceComparisonCrystallinePrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : Fact (JoshiTeich.Prologue.Arithmetic.residueChar s).Prime :=
  LocalCompletion.selectedPrime s

private local instance finitePlaceComparisonCrystallineCharZero {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : CharZero (LocalCompletion.completionAt K s) :=
  LocalCompletion.completionCharZero s

private local instance finitePlaceComparisonCrystallinePrimeNorm {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) :
    Fact (0 < ‖(JoshiTeich.Prologue.Arithmetic.residueChar s : CompletedAlgebraicClosure.Field
        (LocalCompletion.completionAt K s))‖ ∧
      ‖(JoshiTeich.Prologue.Arithmetic.residueChar s : CompletedAlgebraicClosure.Field
        (LocalCompletion.completionAt K s))‖ < 1) :=
  completedPadicPrimeNorm s

local notation "p[" s "]" => JoshiTeich.Prologue.Arithmetic.residueChar s
local notation "E[" s "]" => LocalCompletion.completionAt _ s
local notation "Ω[" s "]" => AlgebraicClosure E[s]
local notation "Ĉ[" s "]" => CompletedAlgebraicClosure.Field E[s]
local notation "C[" s "]" => PadicComplex p[s]
local notation "ι[" s "]" =>
  (UniformSpace.Completion.coeRingHom : CompletedAlgebraicClosure.Algebraic E[s] →+* Ĉ[s])
local notation "j[" s "]" => (algebraicClosureInPadicComplex s : Ω[s] →+* C[s])

local notation "sourceNormedField[" s "]" => (inferInstance : NormedField Ĉ[s])
local notation "sourceUltrametric[" s "]" => CompletedAlgebraicClosure.completedUltrametric E[s]
local notation "sourceComplete[" s "]" => (inferInstance : CompleteSpace Ĉ[s])
local notation "targetNormedField[" s "]" => PadicComplex.normedField p[s]
local notation "targetUltrametric[" s "]" => PadicComplex.isUltrametricDist p[s]
local notation "targetComplete[" s "]" => (inferInstance : CompleteSpace C[s])

/-- The same root tower gives matching crystalline logarithms in both completions. -/
theorem completedPadicCrystallineEquiv_finitePlaceCompletedKummerLog
    {K : Type*} [Field K] [NumberField K] (s : FinitePlace K)
    {a : E[s]} (R : LocalKummer.RootTower (Ω := Ω[s]) p[s] a)
    (ha : ‖j[s] (algebraMap E[s] Ω[s] a)‖ ≤ 1)
    (hu : @IsPrimePrincipal C[s] (targetNormedField[s]) (targetUltrametric[s])
      p[s] (j[s] (algebraMap E[s] Ω[s] a))) :
    completedPadicCrystallineEquiv s (finitePlaceCompletedKummerLog s ha hu R) =
      padicKummerLog p[s] R j[s] ha hu :=
  @equivACris_kummerLogOfExists E[s] Ω[s] _ _ _ Ĉ[s] C[s]
    (sourceNormedField[s]) (sourceUltrametric[s]) (sourceComplete[s])
    (targetNormedField[s]) (targetUltrametric[s]) (targetComplete[s])
    p[s] (LocalCompletion.selectedPrime s) (completedPadicPrimeNorm s) (PadicTiltField.primeNormFact p[s])
    (LocalCompletion.completedPadicEquiv s) (localDeg (K := K) s) (localDeg_pos s)
    (LocalCompletion.completedPadicEquiv_norm_pow s) a R ι[s] j[s]
    (completedPadicEquiv_algebraicClosureInPadicComplex s)
    (CompletedAlgebraicClosure.completedIsAlgClosed E[s]) (PadicComplex.isAlgClosed p[s])
    (finitePlaceCompletedKummerUnit_norm s ha) ha (finitePlaceCompletedKummerUnit_principal s hu) hu

private theorem completedPadicCrystallineEquiv_cocycleLog
    {K : Type*} [Field K] [NumberField K] (s : FinitePlace K)
    {a : E[s]} (R : LocalKummer.RootTower (Ω := Ω[s]) p[s] a)
    (hne : a ≠ 0) (σ : Ω[s] ≃ₐ[E[s]] Ω[s]) :
    completedPadicCrystallineEquiv s (cyclotomicLog Ĉ[s] p[s] (R.mapKummerCocycle ι[s] hne σ)) =
      cyclotomicLog C[s] p[s] (R.mapKummerCocycle j[s] hne σ) :=
  @equivACris_mapKummerCocycle_log E[s] Ω[s] _ _ _ Ĉ[s] C[s]
    (sourceNormedField[s]) (sourceUltrametric[s]) (sourceComplete[s])
    (targetNormedField[s]) (targetUltrametric[s]) (targetComplete[s])
    p[s] (LocalCompletion.selectedPrime s) (completedPadicPrimeNorm s) (PadicTiltField.primeNormFact p[s])
    (LocalCompletion.completedPadicEquiv s) (localDeg (K := K) s) (localDeg_pos s)
    (LocalCompletion.completedPadicEquiv_norm_pow s) a R ι[s] j[s]
    (completedPadicEquiv_algebraicClosureInPadicComplex s) hne σ

/-- In standard `A_cris`, the Galois difference is the logarithm of the same root tower's cocycle. -/
theorem padicCrystallineGalois_finitePlaceKummerLog_sub
    {K : Type*} [Field K] [NumberField K] (s : FinitePlace K)
    {a : E[s]} (R : LocalKummer.RootTower (Ω := Ω[s]) p[s] a)
    (ha : ‖j[s] (algebraMap E[s] Ω[s] a)‖ ≤ 1)
    (hu : @IsPrimePrincipal C[s] (targetNormedField[s]) (targetUltrametric[s])
      p[s] (j[s] (algebraMap E[s] Ω[s] a)))
    (hne : a ≠ 0) (σ : Ω[s] ≃ₐ[E[s]] Ω[s]) :
    padicCrystallineGalois s σ (padicKummerLog p[s] R j[s] ha hu) - padicKummerLog p[s] R j[s] ha hu =
      cyclotomicLog C[s] p[s] (R.mapKummerCocycle j[s] hne σ) := by
  let comparison := completedPadicCrystallineEquiv s
  let completedLog := finitePlaceCompletedKummerLog s ha hu R
  let padicLog := padicKummerLog p[s] R j[s] ha hu
  let completedAction := CompletedAlgebraicClosure.extendGaloisACris p[s] σ
  let padicAction := padicCrystallineGalois s σ
  let cocycleLog := cyclotomicLog Ĉ[s] p[s] (R.mapKummerCocycle ι[s] hne σ)
  have hsub : completedAction completedLog - completedLog = cocycleLog :=
    @CompletedAlgebraicClosure.extendGaloisACris_kummerLogOfExists_sub E[s]
      (LocalCompletion.completionNontrivialNorm s) (LocalCompletion.completionComplete s)
      (LocalCompletion.completionUltrametric s) (LocalCompletion.completionCharZero s)
      p[s] (LocalCompletion.selectedPrime s) (completedPadicPrimeNorm s) a R
      (finitePlaceCompletedKummerUnit_norm s ha) (finitePlaceCompletedKummerUnit_principal s hu) hne σ
  have hLog : comparison completedLog = padicLog :=
    completedPadicCrystallineEquiv_finitePlaceCompletedKummerLog s R ha hu
  have hAction : comparison (completedAction completedLog) = padicAction (comparison completedLog) :=
    completedPadicCrystallineEquiv_extendGaloisACris s σ completedLog
  have hActionLog : comparison (completedAction completedLog) = padicAction padicLog :=
    hAction.trans (congrArg (fun x : ACris C[s] p[s] => padicAction x) hLog)
  calc
    padicAction padicLog - padicLog =
        comparison (completedAction completedLog) - comparison completedLog :=
      congrArg₂ (fun x y : ACris C[s] p[s] => x - y) hActionLog.symm hLog.symm
    _ = comparison (completedAction completedLog - completedLog) :=
      (map_sub comparison _ _).symm
    _ = comparison cocycleLog := congrArg (fun x : ACris Ĉ[s] p[s] => comparison x) hsub
    _ = cyclotomicLog C[s] p[s] (R.mapKummerCocycle j[s] hne σ) :=
      completedPadicCrystallineEquiv_cocycleLog s R hne σ

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
