import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetRhoFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-RHO-PRIME-CALIBRATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, together
with the actual Frobenius rho-seminorm law and prime calibration already
proved on the Frechet completion.
fidelity: records the Frobenius power law on the distinguished actual prime
element. This is an actual-derived calibration consumer; it does not identify
the carrier with paper `B`, define paper rho norms, or supply H1e/BK or
holomorphoid identities. Original proof; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoPrimeCalibration

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

theorem frechetRhoSeminorm_frobenius_prime (ρ : Radius) :
    frechetRhoSeminorm D w (poweredRadius D w ρ)
        (frobeniusEquiv D w
          (originalInclusion D w (Arithmetic.residueChar w.1))) =
      ρ.val.toReal ^ Arithmetic.residueChar w.1 := by
  rw [InitialThetaWittFrechetRhoFrobenius.frechetRhoSeminorm_frobenius,
    frechetRhoSeminorm_prime]

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoPrimeCalibration
