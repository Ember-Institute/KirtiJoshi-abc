import Solutions.Source_ReferenceIutCor312PrimePrincipalTransport
import Solutions.Source_ReferenceIutCor312KummerCrystallineBridge
import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineCompletion
import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineGaloisComparison

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic
open CrystallineEnvelope GeometricTiltComparison

noncomputable section

private def logOfPrimePrincipal {C : Type*} [NormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] (p : ℕ) [Fact p.Prime]
    [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)] {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
    {a : E} (R : LocalKummer.RootTower (Ω := Ω) p a) (j : Ω →+* C)
    (ha : ‖j (algebraMap E Ω a)‖ ≤ 1) (hu : IsPrimePrincipal p (j (algebraMap E Ω a))) :
    ACris C p :=
  kummerLogOfExists C p R j ha hu

attribute [local instance] LocalCompletion.completionNontrivialNorm
  LocalCompletion.completionComplete LocalCompletion.completionUltrametric

local instance finitePlaceCrystallinePrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : Fact (JoshiTeich.Prologue.Arithmetic.residueChar s).Prime :=
  LocalCompletion.selectedPrime s

local instance finitePlaceCrystallineCharZero {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : CharZero (LocalCompletion.completionAt K s) :=
  LocalCompletion.completionCharZero s

local instance finitePlaceCrystallinePrimeNorm {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) :
    Fact (0 < ‖(JoshiTeich.Prologue.Arithmetic.residueChar s : CompletedAlgebraicClosure.Field
        (LocalCompletion.completionAt K s))‖ ∧
      ‖(JoshiTeich.Prologue.Arithmetic.residueChar s : CompletedAlgebraicClosure.Field
        (LocalCompletion.completionAt K s))‖ < 1) :=
  completedPadicPrimeNorm s

variable {K : Type*} [Field K] [NumberField K] (s : FinitePlace K)

local notation "pₛ" => JoshiTeich.Prologue.Arithmetic.residueChar s
local notation "Eₛ" => LocalCompletion.completionAt K s
local notation "Ωₛ" => AlgebraicClosure Eₛ
local notation "Ĉₛ" => CompletedAlgebraicClosure.Field Eₛ
local notation "Cₛ" => PadicComplex pₛ
local notation "eₛ" => LocalCompletion.completedPadicEquiv s
local notation "dₛ" => JoshiTeich.Prologue.Arithmetic.localDeg (K := K) s
local notation "hₛ" => LocalCompletion.completedPadicEquiv_norm_pow s
local notation "ιₛ" =>
  (UniformSpace.Completion.coeRingHom : CompletedAlgebraicClosure.Algebraic Eₛ →+* Ĉₛ)
local notation "jₛ" => (algebraicClosureInPadicComplex s : Ωₛ →+* Cₛ)

local notation "sourceNormedField" => (inferInstance : NormedField Ĉₛ)
local notation "sourceUltrametric" => CompletedAlgebraicClosure.completedUltrametric Eₛ
local notation "sourceComplete" => (inferInstance : CompleteSpace Ĉₛ)
local notation "sourcePrimeNorm" => completedPadicPrimeNorm s
local notation "primeFact" => LocalCompletion.selectedPrime s
local notation "targetNormedField" => PadicComplex.normedField pₛ
local notation "targetUltrametric" => PadicComplex.isUltrametricDist pₛ

/-- The two embeddings of the algebraic closure agree after the completed comparison. -/
theorem completedPadicEquiv_algebraicClosureInPadicComplex (x : Ωₛ) :
    eₛ (ιₛ x) = jₛ x :=
  LocalCompletion.completedPadicEquiv_coe s (show LocalCompletion.AlgebraicCompletion s from x)

/-- A standard integral value is also integral in the spectral-norm completion. -/
theorem finitePlaceCompletedKummerUnit_norm {a : Eₛ}
    (ha : ‖jₛ (algebraMap Eₛ Ωₛ a)‖ ≤ 1) :
    ‖(algebraMap Eₛ Ĉₛ a)‖ ≤ 1 := by
  let z : Ĉₛ := ιₛ (algebraMap Eₛ Ωₛ a)
  change ‖z‖ ≤ 1
  have h : ‖eₛ z‖ ≤ 1 :=
    (congrArg norm (completedPadicEquiv_algebraicClosureInPadicComplex s
      (algebraMap Eₛ Ωₛ a))).symm ▸ ha
  exact (hₛ z).symm.trans_le (pow_le_one₀ (norm_nonneg _) h)

/-- A standard principal-unit value is principal in the spectral-norm completion. -/
theorem finitePlaceCompletedKummerUnit_principal {a : Eₛ}
    (hu : @IsPrimePrincipal Cₛ targetNormedField targetUltrametric pₛ (jₛ (algebraMap Eₛ Ωₛ a))) :
    @IsPrimePrincipal Ĉₛ sourceNormedField sourceUltrametric pₛ (ιₛ (algebraMap Eₛ Ωₛ a)) :=
  @isPrimePrincipal_of_apply_eq Ĉₛ Cₛ sourceNormedField sourceUltrametric
    targetNormedField targetUltrametric eₛ dₛ (localDeg_pos s) hₛ pₛ
    (ιₛ (algebraMap Eₛ Ωₛ a)) (jₛ (algebraMap Eₛ Ωₛ a))
    (completedPadicEquiv_algebraicClosureInPadicComplex s (algebraMap Eₛ Ωₛ a)) hu

/-- The Kummer logarithm of the given root tower in the spectral-norm completion. -/
def finitePlaceCompletedKummerLog {a : Eₛ}
    (ha : ‖jₛ (algebraMap Eₛ Ωₛ a)‖ ≤ 1)
    (hu : @IsPrimePrincipal Cₛ targetNormedField targetUltrametric pₛ (jₛ (algebraMap Eₛ Ωₛ a)))
    (R : LocalKummer.RootTower (Ω := Ωₛ) pₛ a) : ACris Ĉₛ pₛ :=
  @logOfPrimePrincipal Ĉₛ sourceNormedField sourceUltrametric sourceComplete
    (CompletedAlgebraicClosure.completedIsAlgClosed Eₛ) pₛ primeFact sourcePrimeNorm
    Eₛ Ωₛ _ _ _ a R ιₛ
    (finitePlaceCompletedKummerUnit_norm s ha) (finitePlaceCompletedKummerUnit_principal s hu)

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
