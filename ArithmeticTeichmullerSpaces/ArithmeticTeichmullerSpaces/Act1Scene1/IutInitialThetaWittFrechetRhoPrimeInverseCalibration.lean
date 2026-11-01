import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetRhoPrimeCalibration

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-RHO-PRIME-INVERSE-CALIBRATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, together
with the actual inverse Frobenius rho-seminorm law and prime calibration.
fidelity: records the inverse-Frobenius rho calibration on the distinguished
actual prime element. This remains an actual-derived completion result and
does not identify paper `B`, paper rho norms, H1e/BK, or a global holomorphoid.
Original proof; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoPrimeInverseCalibration

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison InitialThetaWittFrechetRhoSeminorm
open InitialThetaWittFrechetFrobenius InitialThetaWittRhoFrobeniusCompletion
open InitialThetaWittAllRadiusCompletion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius
abbrev Completed := InitialThetaWittFrechetComparison.Completed D w

theorem frechetRhoSeminorm_frobenius_inverse_prime (ρ : Radius) :
    frechetRhoSeminorm D w ρ
        ((frobeniusEquiv D w).symm
          (originalInclusion D w (Arithmetic.residueChar w.1))) ^
        Arithmetic.residueChar w.1 =
      (poweredRadius D w ρ).val.toReal := by
  rw [InitialThetaWittFrechetRhoFrobenius.frechetRhoSeminorm_frobenius_inverse,
    frechetRhoSeminorm_prime]

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoPrimeInverseCalibration
