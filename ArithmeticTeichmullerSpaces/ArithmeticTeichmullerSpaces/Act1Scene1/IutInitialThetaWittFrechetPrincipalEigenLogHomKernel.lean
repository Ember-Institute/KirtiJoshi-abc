import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalEigenLogHom
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalRationalLift

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PRINCIPAL-EIGEN-LOG-HOM-KERNEL
source: Joshi II `pr:teichmuller-lift-A`, `eq:tate-module-of-lubin-tate`,
and the multiplicative formal group description of `B^{phi=p}`.
fidelity: transfers the established principal eigen-log image/evaluation
kernel intersection from the principal-unit function to its additive-hom
packaging. The resulting range is exactly the Frechet rational Tate period
range.
boundary: Scene1/Derived; this actual completion range/kernel identity does
not identify paper `B`, define rho norms, or provide H1e/BK, holomorphoid, or
paper theta-volume identities.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalEigenLogHomKernel

open JoshiTeich.Prologue
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open InitialThetaWittFrechetTateKernel
open InitialThetaWittFrechetPrincipalUnitPeriod
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

abbrev Principal := InitialThetaWittPrincipalUnitDomain.Principal D w

theorem frechetPrincipalEigenLogHomRange_inter_evaluationKernel :
    Set.range (frechetPrincipalEigenLogHom D w) ∩
        {x | frechetEigenEvaluation D w x = 0} =
      (frechetEigenPeriodMap D w).range := by
  ext x
  constructor
  · rintro ⟨⟨u, rfl⟩, hu⟩
    have hp : frechetPrincipalEigenLog D w u.toMul ∈
        Set.range (fun p : Principal D w => frechetPrincipalEigenLog D w p) ∩
          {x | frechetEigenEvaluation D w x = 0} := by
      refine ⟨⟨u.toMul, rfl⟩, ?_⟩
      change frechetEigenEvaluation D w
          (frechetPrincipalEigenLog D w u.toMul) = 0
      rw [← frechetPrincipalEigenLogHom_apply D w u]
      exact hu
    rw [frechetPrincipalRange_inter_evaluationKernel D w] at hp
    exact hp
  · rintro ⟨v, rfl⟩
    have hx : frechetEigenPeriodMap D w v ∈
        Set.range (fun p : Principal D w => frechetPrincipalEigenLog D w p) ∩
          {x | frechetEigenEvaluation D w x = 0} := by
      rw [frechetPrincipalRange_inter_evaluationKernel D w]
      exact ⟨v, rfl⟩
    obtain ⟨⟨p, hp⟩, hk⟩ := hx
    refine ⟨⟨Additive.ofMul p, ?_⟩, ?_⟩
    · rw [frechetPrincipalEigenLogHom_apply D w]
      exact hp
    · change frechetEigenEvaluation D w
        (frechetEigenPeriodMap D w v) = 0
      change frechetEigenEvaluation D w
          (frechetEigenPeriodMap D w v) = 0 at hk
      exact hk

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalEigenLogHomKernel
