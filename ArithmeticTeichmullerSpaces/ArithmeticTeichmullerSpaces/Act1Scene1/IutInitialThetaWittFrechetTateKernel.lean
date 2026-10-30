import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFullTateKernel
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateExactSequence

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-TATE-KERNEL
source: Joshi II `pr:teichmuller-lift-A/B` and the actual Tate-period
sequence already proved on the common completion.
fidelity: transports the proved actual full theta-kernel identity and
rational Tate period range through the canonical continuous Padic-algebra
equivalence from the all-radius carrier to the Hausdorff Frechet completion.
No paper B marking, Galois action, or H1e/BK comparison is introduced.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this is an actual Frechet-completion transport,
not an identification with the paper's B.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateKernel

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison
open InitialThetaWittFrechetPadicComparison
open InitialThetaWittAdditiveTatePeriod
open InitialThetaWittRationalTateSource InitialThetaWittRationalTatePeriod
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Scalars := Padic (Arithmetic.residueChar w.1)

def frechetFrobeniusPrime :
    Submodule (Scalars D w) (InitialThetaWittFrechetComparison.Completed D w) :=
  Submodule.comap (InitialThetaWittFrechetPadicComparison.algEquiv D w).toLinearMap
    (frobeniusPrimeSubmodule D w)

def frechetPeriodMap : RationalTate D w →L[Scalars D w]
    InitialThetaWittFrechetComparison.Completed D w :=
  (continuousAlgEquiv D w).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (periodMap D w)

theorem frechetPeriodMap_apply (v : RationalTate D w) :
    frechetPeriodMap D w v =
      (continuousAlgEquiv D w).symm (periodMap D w v) := rfl

theorem frechetPeriodMap_injective : Function.Injective (frechetPeriodMap D w) := by
  intro x y h
  apply periodMap_injective D w
  have h' := congrArg (continuousAlgEquiv D w) h
  simpa only [frechetPeriodMap_apply, (continuousAlgEquiv D w).apply_symm_apply] using h'

theorem mem_fullKernel_iff_mem_frechetPeriodMap_range
    (x : InitialThetaWittFrechetComparison.Completed D w) :
    x ∈ InitialThetaWittFrechetFrobenius.fullKernel D w ↔
      x ∈ (frechetPeriodMap D w).range := by
  constructor
  · intro hx
    have hxactual :
        InitialThetaWittFrechetPadicComparison.algEquiv D w x ∈
          InitialThetaWittEigenKernelTwistedComparison.fullKernel D w :=
      (InitialThetaWittFrechetFrobenius.mem_fullKernel_iff D w x).mp hx
    have hxactual' :
        InitialThetaWittFrechetComparison.ringEquiv D w x ∈
          InitialThetaWittEigenKernelTwistedComparison.fullKernel D w := by
      simpa only [InitialThetaWittFrechetFrobenius.algEquiv_apply] using hxactual
    rw [InitialThetaWittFullTateKernel.fullKernel_eq_periodRange D w] at hxactual'
    obtain ⟨v, hv⟩ := hxactual'
    refine ⟨v, ?_⟩
    apply (InitialThetaWittFrechetComparison.ringEquiv D w).injective
    change (continuousAlgEquiv D w) (frechetPeriodMap D w v) =
      (continuousAlgEquiv D w) x
    rw [frechetPeriodMap_apply, (continuousAlgEquiv D w).apply_symm_apply]
    change periodMap D w v = (InitialThetaWittFrechetComparison.ringEquiv D w) x
    exact hv
  · rintro ⟨v, rfl⟩
    apply (InitialThetaWittFrechetFrobenius.mem_fullKernel_iff D w _).mpr
    have hv : periodMap D w v ∈
        InitialThetaWittEigenKernelTwistedComparison.fullKernel D w := by
      rw [InitialThetaWittFullTateKernel.fullKernel_eq_periodRange D w]
      exact ⟨v, rfl⟩
    change (continuousAlgEquiv D w) (frechetPeriodMap D w v) ∈
      InitialThetaWittEigenKernelTwistedComparison.fullKernel D w
    rw [frechetPeriodMap_apply, (continuousAlgEquiv D w).apply_symm_apply]
    exact hv

theorem fullKernel_eq_frechetPeriodMap_range :
    InitialThetaWittFrechetFrobenius.fullKernel D w =
      (frechetPeriodMap D w).range := by
  ext x
  exact mem_fullKernel_iff_mem_frechetPeriodMap_range D w x

theorem frechetPeriodMap_mem_fullKernel (v : RationalTate D w) :
    frechetPeriodMap D w v ∈ InitialThetaWittFrechetFrobenius.fullKernel D w := by
  exact (mem_fullKernel_iff_mem_frechetPeriodMap_range D w _).mpr ⟨v, rfl⟩

theorem frechetPeriodMap_range_le_fullKernel :
    (frechetPeriodMap D w).range ≤ InitialThetaWittFrechetFrobenius.fullKernel D w := by
  rintro x ⟨v, rfl⟩
  exact frechetPeriodMap_mem_fullKernel D w v

theorem frechetPeriodMap_frobenius_equation (v : RationalTate D w) :
    InitialThetaWittFrechetFrobenius.frobeniusEquiv D w (frechetPeriodMap D w v) =
      (Arithmetic.residueChar w.1 : InitialThetaWittFrechetComparison.Completed D w) *
        frechetPeriodMap D w v := by
  have h := InitialThetaWittFrechetFrobenius.fullKernel_frobenius_equation D w
    ⟨frechetPeriodMap D w v, frechetPeriodMap_mem_fullKernel D w v⟩
  simpa only [Algebra.smul_def, map_natCast] using h

def frechetEigenPeriodMap : RationalTate D w →L[Scalars D w] frechetFrobeniusPrime D w :=
  (frechetPeriodMap D w).codRestrict (frechetFrobeniusPrime D w) (by
    intro v
    change (continuousAlgEquiv D w) (frechetPeriodMap D w v) ∈
      frobeniusPrimeSubmodule D w
    rw [frechetPeriodMap_apply, (continuousAlgEquiv D w).apply_symm_apply]
    exact periodMap_range_le_frobeniusPrime D w ⟨v, rfl⟩)

def frechetTateLine : Submodule (Scalars D w) (frechetFrobeniusPrime D w) :=
  (frechetEigenPeriodMap D w).range

abbrev FrechetTateQuotient := frechetFrobeniusPrime D w ⧸ frechetTateLine D w

def frechetToActualEigen : frechetFrobeniusPrime D w →L[Scalars D w]
    (frobeniusPrimeSubmodule D w) :=
  ((continuousAlgEquiv D w).toContinuousLinearEquiv.toContinuousLinearMap.domRestrict
      (frechetFrobeniusPrime D w)).codRestrict (frobeniusPrimeSubmodule D w) (by
        intro x
        exact x.property)

def actualToFrechetEigen : (frobeniusPrimeSubmodule D w) →L[Scalars D w]
    frechetFrobeniusPrime D w :=
  ((continuousAlgEquiv D w).symm.toContinuousLinearEquiv.toContinuousLinearMap.domRestrict
      (frobeniusPrimeSubmodule D w)).codRestrict (frechetFrobeniusPrime D w) (by
        intro x
        change (InitialThetaWittFrechetPadicComparison.algEquiv D w)
            ((continuousAlgEquiv D w).symm x.1) ∈ frobeniusPrimeSubmodule D w
        rw [InitialThetaWittFrechetFrobenius.algEquiv_apply]
        change (InitialThetaWittFrechetComparison.ringEquiv D w)
            ((InitialThetaWittFrechetComparison.ringEquiv D w).symm x.1) ∈
          frobeniusPrimeSubmodule D w
        rw [RingEquiv.apply_symm_apply]
        exact x.property)

def frechetEigenEvaluation : frechetFrobeniusPrime D w →L[Scalars D w]
    InitialThetaWittThetaBound.Untilt D w :=
  (eigenEvaluation D w).comp (frechetToActualEigen D w)

theorem frechetEigenEvaluation_exact :
    Function.Exact (frechetEigenPeriodMap D w) (frechetEigenEvaluation D w) := by
  apply LinearMap.exact_iff.mpr
  apply le_antisymm
  · intro x hx
    change frechetEigenEvaluation D w x = 0 at hx
    have hxactual : eigenEvaluation D w (frechetToActualEigen D w x) = 0 := hx
    obtain ⟨v, hv⟩ :=
      (InitialThetaWittTateExactSequence.eigenEvaluation_exact D w
        (frechetToActualEigen D w x)).mp hxactual
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply (InitialThetaWittFrechetComparison.ringEquiv D w).injective
    rw [frechetEigenPeriodMap]
    change (InitialThetaWittFrechetComparison.ringEquiv D w)
        (frechetPeriodMap D w v) =
      (InitialThetaWittFrechetComparison.ringEquiv D w) x
    rw [frechetPeriodMap_apply]
    change (continuousAlgEquiv D w) ((continuousAlgEquiv D w).symm (periodMap D w v)) =
      (continuousAlgEquiv D w) x
    rw [(continuousAlgEquiv D w).apply_symm_apply]
    change periodMap D w v = (InitialThetaWittFrechetComparison.ringEquiv D w) x
    exact congrArg Subtype.val hv
  · rintro x ⟨v, rfl⟩
    change frechetEigenEvaluation D w (frechetEigenPeriodMap D w v) = 0
    change eigenEvaluation D w
      (frechetToActualEigen D w (frechetEigenPeriodMap D w v)) = 0
    have hmap : frechetToActualEigen D w (frechetEigenPeriodMap D w v) =
        eigenPeriodMap D w v := by
      apply Subtype.ext
      change (InitialThetaWittFrechetComparison.ringEquiv D w)
          (frechetEigenPeriodMap D w v) = periodMap D w v
      rw [frechetEigenPeriodMap]
      change (InitialThetaWittFrechetComparison.ringEquiv D w)
          (frechetPeriodMap D w v) = periodMap D w v
      rw [frechetPeriodMap_apply]
      change (continuousAlgEquiv D w)
          ((continuousAlgEquiv D w).symm (periodMap D w v)) = periodMap D w v
      rw [(continuousAlgEquiv D w).apply_symm_apply]
    rw [hmap]
    exact congrArg (fun f => f v) (eigenEvaluation_comp_periodMap D w)

theorem frechetToActualEigen_actualToFrechetEigen
    (x : frobeniusPrimeSubmodule D w) :
    frechetToActualEigen D w (actualToFrechetEigen D w x) = x := by
  apply Subtype.ext
  change (InitialThetaWittFrechetPadicComparison.algEquiv D w)
      ((continuousAlgEquiv D w).symm x.1) = x.1
  exact (InitialThetaWittFrechetPadicComparison.algEquiv D w).apply_symm_apply x.1

theorem actualToFrechetEigen_frechetToActualEigen
    (x : frechetFrobeniusPrime D w) :
    actualToFrechetEigen D w (frechetToActualEigen D w x) = x := by
  apply Subtype.ext
  change (continuousAlgEquiv D w).symm
      ((InitialThetaWittFrechetPadicComparison.algEquiv D w) x.1) = x.1
  exact (continuousAlgEquiv D w).symm_apply_apply x.1

theorem frechetToActualEigen_injective : Function.Injective (frechetToActualEigen D w) := by
  intro x y h
  have h' := congrArg (actualToFrechetEigen D w) h
  rw [actualToFrechetEigen_frechetToActualEigen D w x,
    actualToFrechetEigen_frechetToActualEigen D w y] at h'
  exact h'

theorem frechetToActualEigen_surjective :
    Function.Surjective (frechetToActualEigen D w) := by
  intro y
  exact ⟨actualToFrechetEigen D w y,
    frechetToActualEigen_actualToFrechetEigen D w y⟩

def frechetToActualEigenLinearEquiv :
    frechetFrobeniusPrime D w ≃ₗ[Scalars D w] frobeniusPrimeSubmodule D w where
  toFun := frechetToActualEigen D w
  invFun := actualToFrechetEigen D w
  left_inv := actualToFrechetEigen_frechetToActualEigen D w
  right_inv := frechetToActualEigen_actualToFrechetEigen D w
  map_add' := map_add (frechetToActualEigen D w)
  map_smul' := map_smul (frechetToActualEigen D w)

def frechetToActualEigenContinuousLinearEquiv :
    frechetFrobeniusPrime D w ≃L[Scalars D w] frobeniusPrimeSubmodule D w where
  toLinearEquiv := frechetToActualEigenLinearEquiv D w
  continuous_toFun := (frechetToActualEigen D w).continuous
  continuous_invFun := (actualToFrechetEigen D w).continuous

theorem frechetEigenPeriodMap_injective :
    Function.Injective (frechetEigenPeriodMap D w) := by
  intro x y h
  apply frechetPeriodMap_injective D w
  exact congrArg Subtype.val h

theorem frechetEigenPeriodMap_isClosedEmbedding :
    Topology.IsClosedEmbedding (frechetEigenPeriodMap D w) :=
  LinearMap.isClosedEmbedding_of_injective
    (f := (frechetEigenPeriodMap D w).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (frechetEigenPeriodMap_injective D w))

theorem frechetEigenEvaluation_isOpenMap :
    IsOpenMap (frechetEigenEvaluation D w) := by
  have h := (InitialThetaWittEigenEvaluationOpen.eigenEvaluation_isOpenMap D w).comp
    (frechetToActualEigenContinuousLinearEquiv D w).toHomeomorph.isOpenMap
  have heq : (fun x => eigenEvaluation D w
      ((frechetToActualEigenContinuousLinearEquiv D w).toHomeomorph x)) =
      frechetEigenEvaluation D w := by
    funext x
    rfl
  rw [← heq]
  exact h

theorem frechetEigenEvaluation_isOpenQuotientMap :
    IsOpenQuotientMap (frechetEigenEvaluation D w) :=
  ⟨(InitialThetaWittEigenEvaluationSurjective.eigenEvaluation_surjective D w).comp
      (frechetToActualEigen_surjective D w),
    (eigenEvaluation D w).continuous.comp (frechetToActualEigen D w).continuous,
    frechetEigenEvaluation_isOpenMap D w⟩

theorem frechetTatePeriodSequence_strictExact :
    Topology.IsClosedEmbedding (frechetEigenPeriodMap D w) ∧
      Function.Exact (frechetEigenPeriodMap D w) (frechetEigenEvaluation D w) ∧
        IsOpenQuotientMap (frechetEigenEvaluation D w) :=
  ⟨frechetEigenPeriodMap_isClosedEmbedding D w,
    frechetEigenEvaluation_exact D w,
    frechetEigenEvaluation_isOpenQuotientMap D w⟩

theorem frechetEigenEvaluation_actualToFrechet
    (x : frobeniusPrimeSubmodule D w) :
    frechetEigenEvaluation D w (actualToFrechetEigen D w x) =
      eigenEvaluation D w x := by
  change eigenEvaluation D w
    (frechetToActualEigen D w (actualToFrechetEigen D w x)) = _
  rw [frechetToActualEigen_actualToFrechetEigen]

theorem frechetTateLine_le_evaluationKernel :
    frechetTateLine D w ≤ (frechetEigenEvaluation D w).ker :=
  (LinearMap.exact_iff.mp (frechetEigenEvaluation_exact D w)).symm.le

def frechetQuotientEvaluation : FrechetTateQuotient D w →L[Scalars D w]
    InitialThetaWittThetaBound.Untilt D w :=
  (frechetTateLine D w).liftQL (frechetEigenEvaluation D w)
    (frechetTateLine_le_evaluationKernel D w)

theorem frechetQuotientEvaluation_mk (x : frechetFrobeniusPrime D w) :
    frechetQuotientEvaluation D w (Submodule.Quotient.mk x) =
      frechetEigenEvaluation D w x := rfl

theorem frechetQuotientEvaluation_surjective :
    Function.Surjective (frechetQuotientEvaluation D w) := by
  intro y
  obtain ⟨x, hx⟩ :=
    InitialThetaWittEigenEvaluationSurjective.eigenEvaluation_surjective D w y
  exact ⟨Submodule.Quotient.mk (actualToFrechetEigen D w x),
    (frechetQuotientEvaluation_mk D w _).trans
      ((frechetEigenEvaluation_actualToFrechet D w x).trans hx)⟩

theorem frechetQuotientEvaluation_injective :
    Function.Injective (frechetQuotientEvaluation D w) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot (frechetTateLine D w)
    (frechetEigenEvaluation D w).toLinearMap
    (frechetTateLine_le_evaluationKernel D w)
    (LinearMap.exact_iff.mp (frechetEigenEvaluation_exact D w)).le

theorem frechetQuotientEvaluation_continuous :
    Continuous (frechetQuotientEvaluation D w) :=
  (frechetQuotientEvaluation D w).continuous

theorem frechetQuotientEvaluation_isOpenMap :
    IsOpenMap (frechetQuotientEvaluation D w) := by
  apply (frechetTateLine D w).isOpenQuotientMap_mkQL.isOpenMap_iff.mpr
  have heq : (fun x =>
      frechetQuotientEvaluation D w ((frechetTateLine D w).mkQL x)) =
      frechetEigenEvaluation D w := by
    funext x
    exact frechetQuotientEvaluation_mk D w x
  change IsOpenMap (fun x =>
    frechetQuotientEvaluation D w ((frechetTateLine D w).mkQL x))
  rw [heq]
  exact frechetEigenEvaluation_isOpenMap D w

theorem frechetQuotientEvaluation_isOpenQuotientMap :
    IsOpenQuotientMap (frechetQuotientEvaluation D w) :=
  ⟨frechetQuotientEvaluation_surjective D w,
    frechetQuotientEvaluation_continuous D w,
    frechetQuotientEvaluation_isOpenMap D w⟩

def frechetQuotientEvaluationContinuousLinearEquiv :
    FrechetTateQuotient D w ≃L[Scalars D w]
      InitialThetaWittThetaBound.Untilt D w := by
  let e : FrechetTateQuotient D w ≃ₗ[Scalars D w]
      InitialThetaWittThetaBound.Untilt D w :=
    LinearEquiv.ofBijective (frechetQuotientEvaluation D w).toLinearMap
      ⟨frechetQuotientEvaluation_injective D w,
        frechetQuotientEvaluation_surjective D w⟩
  exact { e with
    continuous_toFun := frechetQuotientEvaluation_continuous D w
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen
      (frechetQuotientEvaluation_continuous D w)
      (frechetQuotientEvaluation_isOpenMap D w)).continuous_invFun }

theorem frechetQuotientEvaluationContinuousLinearEquiv_apply
    (x : FrechetTateQuotient D w) :
    frechetQuotientEvaluationContinuousLinearEquiv D w x =
      frechetQuotientEvaluation D w x := rfl

def frechetTateQuotientToActual :
    FrechetTateQuotient D w ≃L[Scalars D w]
      InitialThetaWittTateBanachQuotient.TateQuotient D w :=
  (frechetQuotientEvaluationContinuousLinearEquiv D w).trans
    (InitialThetaWittTateExactSequence.quotientEvaluationContinuousLinearEquiv D w).symm

theorem frechetTateQuotientToActual_apply (x : FrechetTateQuotient D w) :
    frechetTateQuotientToActual D w x =
      (InitialThetaWittTateExactSequence.quotientEvaluationContinuousLinearEquiv D w).symm
        (frechetQuotientEvaluationContinuousLinearEquiv D w x) := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateKernel
