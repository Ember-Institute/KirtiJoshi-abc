import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoCompletionSource
import ArithmeticTeichmullerSpaces.Act1Scene1.NormPowerRingEquiv

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-COMPLETION-COMPARISON
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the fixed-rho
normed completions of the bounded Witt period ring, with the proved
actual-to-standard local-degree norm comparison.
fidelity: extends the original bounded-ring equivalence from actual radius
rho^localDeg to independent standard radius rho. The norm power law proves
uniform continuity in both directions and remains true on the completions.
The completed ring equivalence fixes the original bounded inclusion. Both
norms and the p-only standard completion retain their original definitions.
Original proofs; Scene1/Derived; Prologue R5 unchanged.
boundary: all-radius Frechet comparison, paper B and period/BK identities
are separate obligations. No isometry is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoCompletionComparison

open JoshiTeich.Prologue
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeCompletionComparison : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem source_uniformContinuous (ρ : Radius) :
    UniformContinuous (sourceRingEquiv D w ρ) :=
  NormPowerRingEquiv.uniformContinuous (sourceRingEquiv D w ρ)
    (Arithmetic.localDeg w.1) (source_norm_pow D w ρ)

theorem source_symm_uniformContinuous (ρ : Radius) :
    UniformContinuous (sourceRingEquiv D w ρ).symm :=
  NormPowerRingEquiv.symm_uniformContinuous (sourceRingEquiv D w ρ)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (source_norm_pow D w ρ)

def completedRingEquiv (ρ : Radius) :
    InitialThetaWittRhoCompletion.Completed D w (actualRadius D w ρ) ≃+*
      PadicWittRhoCompletion.Completed (Arithmetic.residueChar w.1) ρ :=
  NormPowerRingEquiv.completedRingEquiv (sourceRingEquiv D w ρ)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (source_norm_pow D w ρ)

theorem completedRingEquiv_continuous (ρ : Radius) :
    Continuous (completedRingEquiv D w ρ) :=
  NormPowerRingEquiv.completedRingEquiv_continuous (sourceRingEquiv D w ρ)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (source_norm_pow D w ρ)

theorem completedRingEquiv_symm_continuous (ρ : Radius) :
    Continuous (completedRingEquiv D w ρ).symm :=
  NormPowerRingEquiv.completedRingEquiv_symm_continuous (sourceRingEquiv D w ρ)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (source_norm_pow D w ρ)

theorem completedRingEquiv_coe (ρ : Radius)
    (x : InitialThetaWittRhoCompletion.Source D w (actualRadius D w ρ)) :
    completedRingEquiv D w ρ
        (UniformSpace.Completion.coeRingHom x) =
      UniformSpace.Completion.coeRingHom (sourceRingEquiv D w ρ x) :=
  NormPowerRingEquiv.completedRingEquiv_coe (sourceRingEquiv D w ρ)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (source_norm_pow D w ρ) x

theorem completedRingEquiv_norm_pow (ρ : Radius)
    (x : InitialThetaWittRhoCompletion.Completed D w (actualRadius D w ρ)) :
    ‖completedRingEquiv D w ρ x‖ ^ Arithmetic.localDeg w.1 = ‖x‖ :=
  NormPowerRingEquiv.completedRingEquiv_norm_pow (sourceRingEquiv D w ρ)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (source_norm_pow D w ρ) x

def completedHomeomorph (ρ : Radius) :
    InitialThetaWittRhoCompletion.Completed D w (actualRadius D w ρ) ≃ₜ
      PadicWittRhoCompletion.Completed (Arithmetic.residueChar w.1) ρ :=
  NormPowerRingEquiv.completedHomeomorph (sourceRingEquiv D w ρ)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (source_norm_pow D w ρ)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoCompletionComparison
