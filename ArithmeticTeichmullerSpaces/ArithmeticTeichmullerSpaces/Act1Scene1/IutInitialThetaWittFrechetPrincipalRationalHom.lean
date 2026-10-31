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

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalRationalHom
