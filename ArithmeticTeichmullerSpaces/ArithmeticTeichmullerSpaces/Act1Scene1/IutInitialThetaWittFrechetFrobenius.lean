import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPadicComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenKernelTwistedComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-FROBENIUS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, together with
the actual all-radius completion comparison already proved in Scene1.
fidelity: transports the actual Frobenius automorphism and the actual
theta/Frobenius kernel from the diagonal-closure carrier to its canonical
Hausdorff completion. This is an actual Frechet-completion transport; it
does not identify that completion with the paper's `B`.
boundary: Scene1/Derived; paper `B`, Tate-period classification and BK
comparison remain separate obligations. Original carrier and R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetFrobenius

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison InitialThetaWittFrechetPadicComparison
open InitialThetaWittEigenKernelTwistedComparison
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Completed := InitialThetaWittFrechetComparison.Completed D w
abbrev Carrier := InitialThetaWittFrechetComparison.Carrier D w
abbrev Scalars := Padic (Arithmetic.residueChar w.1)

def frobeniusEquiv : Completed D w ≃+* Completed D w :=
  (ringEquiv D w).trans ((InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).trans
    (ringEquiv D w).symm)

theorem frobeniusEquiv_apply (x : Completed D w) :
    ringEquiv D w (frobeniusEquiv D w x) =
      InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (ringEquiv D w x) := by
  simp [frobeniusEquiv]

theorem frobeniusEquiv_continuous : Continuous (frobeniusEquiv D w) := by
  exact (ringEquiv_symm_continuous D w).comp <|
    (InitialThetaWittAllRadiusFrobenius.frobenius_continuous D w).comp
      (ringEquiv_continuous D w)

theorem frobeniusEquiv_symm_continuous : Continuous (frobeniusEquiv D w).symm := by
  have h₁ : Continuous (fun x =>
      (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).symm
        ((ringEquiv D w) x)) :=
    (InitialThetaWittAllRadiusFrobenius.inverse_continuous D w).comp
      (ringEquiv_continuous D w)
  have h₂ : Continuous (fun x =>
      (ringEquiv D w).symm
        ((InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).symm
          ((ringEquiv D w) x))) :=
    (ringEquiv_symm_continuous D w).comp h₁
  change Continuous (fun x =>
    (ringEquiv D w).symm
      ((InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).symm
        ((ringEquiv D w) x)))
  exact h₂

theorem algEquiv_apply (x : Completed D w) :
    InitialThetaWittFrechetPadicComparison.algEquiv D w x = ringEquiv D w x := rfl

def fullKernel : Submodule (Scalars D w) (Completed D w) :=
  Submodule.comap (InitialThetaWittFrechetPadicComparison.algEquiv D w).toLinearMap
    (InitialThetaWittEigenKernelTwistedComparison.fullKernel D w)

theorem mem_fullKernel_iff (x : Completed D w) :
    x ∈ fullKernel D w ↔
      InitialThetaWittFrechetPadicComparison.algEquiv D w x ∈
        InitialThetaWittEigenKernelTwistedComparison.fullKernel D w :=
  Iff.rfl

theorem fullKernel_frobenius_equation (x : fullKernel D w) :
    frobeniusEquiv D w x.val =
      (Arithmetic.residueChar w.1 : Scalars D w) • x.val := by
  apply (InitialThetaWittFrechetPadicComparison.algEquiv D w).injective
  have htransport :
      InitialThetaWittFrechetPadicComparison.algEquiv D w
          (frobeniusEquiv D w x.val) =
        InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
          (InitialThetaWittFrechetPadicComparison.algEquiv D w x.val) := by
    change ringEquiv D w (frobeniusEquiv D w x.val) = _
    exact frobeniusEquiv_apply D w x.val
  rw [htransport, map_smul]
  have hxactualAlg := (mem_fullKernel_iff D w x.val).mp x.property
  have hxactual : ringEquiv D w x.val ∈
      InitialThetaWittEigenKernelTwistedComparison.fullKernel D w := by
    change InitialThetaWittFrechetPadicComparison.algEquiv D w x.val ∈ _
    exact hxactualAlg
  have hact := (mem_fullKernel D w (ringEquiv D w x.val)).mp hxactual |>.1
  simp only [algEquiv_apply, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  exact hact

theorem fullKernel_theta_equation (x : fullKernel D w) :
    InitialThetaWittThetaEvaluation.evaluation D w (ringEquiv D w x.val) = 0 :=
  by
    have hxactualAlg := (mem_fullKernel_iff D w x.val).mp x.property
    have hxactual : ringEquiv D w x.val ∈
        InitialThetaWittEigenKernelTwistedComparison.fullKernel D w := by
      change InitialThetaWittFrechetPadicComparison.algEquiv D w x.val ∈ _
      exact hxactualAlg
    exact (mem_fullKernel D w (ringEquiv D w x.val)).mp hxactual |>.2

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetFrobenius
