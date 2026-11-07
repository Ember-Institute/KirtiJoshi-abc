import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalEigenLogHom
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalPrimeDivision

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PRINCIPAL-PRIME-DIVISION
source: Joshi II `eq:tate-module-of-lubin-tate` and the actual principal
unit p-power root law transported through the Fréchet completion comparison.
fidelity: proves that the actual inverse-Frobenius p^k root on the principal
tilt units maps under the Fréchet eigen logarithm to multiplication by p^-k.
The proof uses the existing actual eigen-log root law and the original
Fréchet-to-actual linear equivalence.
boundary: Scene1/Derived; this is finite p-power scalar compatibility. It
does not give the principal-unit group a Q_p-module structure or identify the
constructed Fréchet completion with paper `B`.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalPrimeDivision

open JoshiTeich.Prologue
open InitialThetaWittPrincipalUnitDomain
open InitialThetaWittFrechetPrincipalEigenLogHom
open InitialThetaWittPrincipalPrimeDivision
open InitialThetaWittFrechetTateKernel
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

theorem frechetPrincipalEigenLogHom_primeRoot (k : ℕ) (u : Principal D w) :
    frechetPrincipalEigenLogHom D w
        (Additive.ofMul (primeRoot D w k u)) =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ •
        frechetPrincipalEigenLogHom D w (Additive.ofMul u) := by
  apply frechetToActualEigen_injective D w
  rw [frechetToActualEigen_frechetPrincipalEigenLogHom D w
      (Additive.ofMul (primeRoot D w k u)),
    map_smul,
    frechetToActualEigen_frechetPrincipalEigenLogHom D w (Additive.ofMul u)]
  exact eigenLogHom_primeRoot D w k u

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPrincipalPrimeDivision
