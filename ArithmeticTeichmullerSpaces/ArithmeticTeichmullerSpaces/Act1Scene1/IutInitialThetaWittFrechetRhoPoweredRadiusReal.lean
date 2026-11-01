import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetRhoPrimeInverseCalibration

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-RHO-POWERED-RADIUS-REAL
source: Joshi II `se:ff-rings`, the actual rho radius-power map, and the
proved inverse Frobenius prime calibration.
fidelity: exposes the real-valued form of the powered-radius map and rewrites
the inverse prime calibration with the explicit numerical factor
`(rho.toReal)^p`. This is actual-derived normalization only; it does not
identify paper `B`, paper rho norms, H1e/BK, or global holomorphoid data.
Original proof; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoPoweredRadiusReal

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison InitialThetaWittFrechetRhoSeminorm
open InitialThetaWittFrechetFrobenius InitialThetaWittRhoFrobeniusCompletion
open InitialThetaWittAllRadiusCompletion
open InitialThetaWittFrechetRhoPrimeInverseCalibration
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

theorem poweredRadius_toReal (ρ : Radius) :
    (poweredRadius D w ρ).val.toReal = ρ.val.toReal ^ Arithmetic.residueChar w.1 := by
  change (ρ.val ^ Arithmetic.residueChar w.1).toReal = _
  rw [ENNReal.toReal_pow]

theorem frechetRhoSeminorm_frobenius_inverse_prime_explicit (ρ : Radius) :
    frechetRhoSeminorm D w ρ
        ((frobeniusEquiv D w).symm
          (originalInclusion D w (Arithmetic.residueChar w.1))) ^
        Arithmetic.residueChar w.1 =
      ρ.val.toReal ^ Arithmetic.residueChar w.1 := by
  rw [frechetRhoSeminorm_frobenius_inverse_prime, poweredRadius_toReal]

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoPoweredRadiusReal
