import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalEigenLogHom
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalRationalLift

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PRINCIPAL-RATIONAL-HOM
source: Joshi II `eq:tate-module-of-lubin-tate` and the period sequence
in the proof of `pr:teichmuller-lift-A`.
fidelity: packages the transported rational principal-unit lift as an
additive homomorphism from the actual rational Tate source. Its value is the
Fréchet rational Tate period map, so injectivity is inherited from the actual
period map.
boundary: Scene1/Derived; this is an actual completion transport. It does not
identify paper `B`, define rho norms, or provide H1e/BK, holomorphoid, paper
representative, or theta-volume identities.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalRationalHom

open JoshiTeich.Prologue
open InitialThetaWittRationalTateSource InitialThetaWittRationalTatePrincipalLift
open InitialThetaWittFrechetTateKernel
open InitialThetaWittFrechetPrincipalEigenLogHom
open InitialThetaWittFrechetPrincipalRationalLift
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev RationalTate := InitialThetaWittRationalTateSource.RationalTate D w

def frechetPrincipalRationalHom : RationalTate D w →+
    InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w :=
  (frechetPrincipalEigenLogHom D w).comp
    (InitialThetaWittRationalTatePrincipalLift.rationalPrincipalHom D w)

theorem frechetPrincipalRationalHom_apply (v : RationalTate D w) :
    frechetPrincipalRationalHom D w v =
      frechetPrincipalRational D w v := by
  apply Subtype.ext
  rfl

theorem frechetPrincipalRationalHom_eq_frechetEigenPeriodMap
    (v : RationalTate D w) :
    frechetPrincipalRationalHom D w v =
      InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap D w v := by
  rw [frechetPrincipalRationalHom_apply]
  exact frechetPrincipalRational_eq_frechetEigenPeriodMap D w v

theorem frechetPrincipalRationalHom_injective :
    Function.Injective (frechetPrincipalRationalHom D w) := by
  intro v z h
  apply InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap_injective D w
  exact (frechetPrincipalRationalHom_eq_frechetEigenPeriodMap D w v).symm.trans
    (h.trans (frechetPrincipalRationalHom_eq_frechetEigenPeriodMap D w z))

theorem frechetPrincipalRationalHom_exact :
    Function.Exact (frechetPrincipalRationalHom D w)
      (InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w) := by
  intro x
  constructor
  · intro hx
    obtain ⟨v, hv⟩ :=
      (InitialThetaWittFrechetTateKernel.frechetEigenEvaluation_exact D w x).mp hx
    refine ⟨v, ?_⟩
    exact (frechetPrincipalRationalHom_eq_frechetEigenPeriodMap D w v).trans hv
  · rintro ⟨v, rfl⟩
    rw [frechetPrincipalRationalHom_eq_frechetEigenPeriodMap]
    exact (InitialThetaWittFrechetTateKernel.frechetEigenEvaluation_exact D w
      (InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap D w v)).mpr ⟨v, rfl⟩

theorem frechetPrincipalRationalHom_range :
    Set.range (frechetPrincipalRationalHom D w) =
      (InitialThetaWittFrechetTateKernel.frechetEigenPeriodMap D w).range := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, (frechetPrincipalRationalHom_eq_frechetEigenPeriodMap D w v).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, frechetPrincipalRationalHom_eq_frechetEigenPeriodMap D w v⟩

theorem frechetPrincipalRationalHom_mem_tateLine (v : RationalTate D w) :
    frechetPrincipalRationalHom D w v ∈
      InitialThetaWittFrechetTateKernel.frechetTateLine D w := by
  rw [frechetPrincipalRationalHom_eq_frechetEigenPeriodMap]
  exact ⟨v, rfl⟩

theorem frechetPrincipalRationalHom_evaluation (v : RationalTate D w) :
    InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w
        (frechetPrincipalRationalHom D w v) = 0 := by
  rw [frechetPrincipalRationalHom_eq_frechetEigenPeriodMap]
  exact (InitialThetaWittFrechetTateKernel.frechetEigenEvaluation_exact D w _).mpr
    ⟨v, rfl⟩

theorem frechetPrincipalRationalHom_range_eq_evaluationKernel :
    Set.range (frechetPrincipalRationalHom D w) =
      {x | InitialThetaWittFrechetTateKernel.frechetEigenEvaluation D w x = 0} := by
  rw [frechetPrincipalRationalHom_range]
  ext x
  exact (InitialThetaWittFrechetTateKernel.frechetEigenEvaluation_exact D w x).symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalRationalHom
