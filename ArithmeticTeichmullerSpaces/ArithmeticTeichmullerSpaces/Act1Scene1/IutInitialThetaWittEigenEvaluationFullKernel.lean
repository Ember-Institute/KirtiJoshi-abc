import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateBanachQuotient
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenKernelTwistedComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-EVALUATION-FULL-KERNEL
source: Joshi II `pr:teichmuller-lift-A` and the actual theta/Frobenius
subspaces proved in Scene1.
fidelity: identifies the kernel of the actual evaluation on the complete
phi=p subspace with the previously defined full theta kernel, without
replacing the carrier by a smaller period image.
boundary: Scene1/Derived; no Tate-kernel equality or injectivity of the
Tate quotient evaluation is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenEvaluationFullKernel

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittRationalTatePeriod
open InitialThetaWittEigenKernelTwistedComparison
open InitialThetaWittAdditiveTatePeriod
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem eigenEvaluation_zero_iff_fullKernel
    (x : frobeniusPrimeSubmodule D w) :
    eigenEvaluation D w x = 0 ↔ x.1 ∈ fullKernel D w := by
  change InitialThetaWittThetaEvaluation.evaluation D w x.1 = 0 ↔ _
  rw [mem_fullKernel]
  constructor
  · intro h
    have hphi : InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x.1 =
        (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x.1 := by
      have hx := x.2
      change x.1 ∈ {z : Carrier D w |
        InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w z =
          (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • z} at hx
      simpa only [Set.mem_setOf_eq] using hx
    exact ⟨by simpa only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using hphi, h⟩
  · intro h
    exact h.2

theorem eigenEvaluation_kernel_val_eq_fullKernel :
    {x : frobeniusPrimeSubmodule D w | eigenEvaluation D w x = 0}.image
      (fun x => x.1) = (fullKernel D w : Set (Carrier D w)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (eigenEvaluation_zero_iff_fullKernel D w y).mp hy
  · intro hx
    let y : frobeniusPrimeSubmodule D w := ⟨x, hx.1⟩
    refine ⟨y, (eigenEvaluation_zero_iff_fullKernel D w y).mpr ?_, rfl⟩
    exact hx

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenEvaluationFullKernel
