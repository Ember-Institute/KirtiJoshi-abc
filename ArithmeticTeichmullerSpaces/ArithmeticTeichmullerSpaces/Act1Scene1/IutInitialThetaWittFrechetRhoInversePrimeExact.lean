import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetRhoPoweredRadiusReal

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-RHO-INVERSE-PRIME-EXACT
source: Joshi II `se:ff-rings`, the actual rho radius-power law, and the
inverse Frobenius prime calibration.
fidelity: removes the p-th power from the existing inverse-prime rho
calibration using nonnegativity of the actual seminorm and the positive
prime exponent. This is an exact actual-derived rho value statement.
boundary: this does not identify the actual seminorm with the paper rho norm
or the carrier with paper B, and does not provide H1e/BK or holomorphoid laws.
Original proof; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoInversePrimeExact

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison InitialThetaWittFrechetRhoSeminorm
open InitialThetaWittFrechetFrobenius
open InitialThetaWittFrechetRhoPoweredRadiusReal
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

theorem frechetRhoSeminorm_frobenius_inverse_prime_eq (ρ : Radius) :
    frechetRhoSeminorm D w ρ
        ((InitialThetaWittFrechetFrobenius.frobeniusEquiv D w).symm
          (InitialThetaWittFrechetComparison.originalInclusion D w
            (Arithmetic.residueChar w.1))) =
      ρ.val.toReal := by
  apply (pow_left_inj₀ (by
    rw [frechetRhoSeminorm_apply]
    exact norm_nonneg _) (ENNReal.toReal_nonneg)
    (Nat.ne_of_gt (Arithmetic.residueChar_prime w.1).pos)).mp
  exact frechetRhoSeminorm_frobenius_inverse_prime_explicit D w ρ

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoInversePrimeExact
