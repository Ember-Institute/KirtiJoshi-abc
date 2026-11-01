import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetRhoSeminorm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-RHO-FROBENIUS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, together
with the locally proved actual radius-power law.
fidelity: transports the actual radius-power law for Frobenius to the
rho-seminorm family on the Frechet completion.
boundary: Scene1/Derived; this does not identify the carrier with paper `B`
or define the paper's rho-norm.  Original proof; no reference implementation
copied.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoFrobenius

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

theorem frechetRhoSeminorm_frobenius (ρ : Radius) (x : Completed D w) :
    frechetRhoSeminorm D w (poweredRadius D w ρ) (frobeniusEquiv D w x) =
      frechetRhoSeminorm D w ρ x ^ Arithmetic.residueChar w.1 := by
  change coordinateSeminorm D w (poweredRadius D w ρ)
      (ringEquiv D w (frobeniusEquiv D w x)) =
    coordinateSeminorm D w ρ (ringEquiv D w x) ^ Arithmetic.residueChar w.1
  rw [InitialThetaWittFrechetFrobenius.frobeniusEquiv_apply,
    InitialThetaWittAllRadiusFrobenius.coordinateSeminorm_frobenius]

theorem frechetRhoSeminorm_frobenius_inverse (ρ : Radius) (x : Completed D w) :
    frechetRhoSeminorm D w ρ ((frobeniusEquiv D w).symm x) ^
        Arithmetic.residueChar w.1 =
      frechetRhoSeminorm D w (poweredRadius D w ρ) x := by
  have h := frechetRhoSeminorm_frobenius D w ρ ((frobeniusEquiv D w).symm x)
  simpa only [RingEquiv.apply_symm_apply] using h.symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoFrobenius
