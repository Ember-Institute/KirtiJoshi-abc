import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalEigenLogHomKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PRINCIPAL-EIGEN-LOG-HOM-SURJECTIVE
source: Joshi III `th:B-is-gen-in-deg-one`, first item, together with the
actual Frechet Tate exact sequence and the principal-unit range/kernel law.
fidelity: classifies every element of the constructed actual Frechet
`phi=p` submodule as the eigen logarithm of a unique principal-unit element.
The proof is algebraic and uses the existing evaluation surjectivity,
exactness, and eigen-log range/kernel intersection.
boundary: Scene1/Derived; this does not identify the constructed completion
with paper `B`, supply a rho norm or Frechet topology for paper `B`, or prove
H1e/BK, holomorphoid, paper representative, or theta-volume identities.
Original proof; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalEigenLogHomSurjective

open JoshiTeich.Prologue
open InitialThetaWittPrincipalUnitDomain
open InitialThetaWittFrechetTateKernel
open InitialThetaWittFrechetPrincipalEigenLogHom
open InitialThetaWittFrechetPrincipalEigenLogHomKernel
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Principal := InitialThetaWittPrincipalUnitDomain.Principal D w

theorem frechetPrincipalEigenLogHom_surjective :
    Function.Surjective (frechetPrincipalEigenLogHom D w) := by
  intro x
  obtain ⟨u, hu⟩ :=
    frechetPrincipalEvaluationHom_surjective D w
      (frechetEigenEvaluation D w x)
  have hdiff :
      frechetEigenEvaluation D w
        (x - frechetPrincipalEigenLogHom D w u) = 0 := by
    rw [map_sub]
    change frechetEigenEvaluation D w x -
      frechetPrincipalEvaluationHom D w u = 0
    rw [hu, sub_self]
  have hmem :
      x - frechetPrincipalEigenLogHom D w u ∈
        Set.range (frechetPrincipalEigenLogHom D w) ∩
          {z | frechetEigenEvaluation D w z = 0} := by
    rw [frechetPrincipalEigenLogHomRange_inter_evaluationKernel D w]
    exact (frechetEigenEvaluation_exact D w
      (x - frechetPrincipalEigenLogHom D w u)).mp hdiff
  obtain ⟨v, hv⟩ := hmem.1
  refine ⟨v + u, ?_⟩
  rw [map_add, hv]
  exact sub_add_cancel _ _

theorem frechetPrincipalEigenLogHom_bijective :
    Function.Bijective (frechetPrincipalEigenLogHom D w) :=
  ⟨frechetPrincipalEigenLogHom_injective D w,
    frechetPrincipalEigenLogHom_surjective D w⟩

def frechetPrincipalEigenLogAddEquiv :
    Additive (Principal D w) ≃+
      frechetFrobeniusPrime D w :=
  AddEquiv.ofBijective (frechetPrincipalEigenLogHom D w)
    (frechetPrincipalEigenLogHom_bijective D w)

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalEigenLogHomSurjective
