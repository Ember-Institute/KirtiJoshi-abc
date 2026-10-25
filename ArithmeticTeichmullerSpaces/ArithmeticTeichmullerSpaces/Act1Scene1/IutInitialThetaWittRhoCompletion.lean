import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoNorm
import Mathlib.Analysis.Normed.Module.Completion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-COMPLETION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, completion
of the bounded Witt period subring at a fixed rho.
fidelity: puts the proved rho RingNorm on a separate copy of the actual
bounded Witt localization and forms its normed-ring completion. The
original ring embeds injectively with dense image and preserved norm.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this is a single-radius completion. A common
Frechet completion, multiplicative norm equality, period identities and
BK comparisons remain open. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoCompletion

open JoshiTeich.Prologue
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Radius := {ρ : ℝ≥0∞ // 0 < ρ ∧ ρ < 1}

/-- A separate copy allows each radius its own norm and uniform structure. -/
def Source (_ρ : Radius) : Type u := InitialThetaBoundedWittLocalization.Ring D w

variable (ρ : Radius)

instance sourceCommRing : CommRing (Source D w ρ) :=
  inferInstanceAs (CommRing (InitialThetaBoundedWittLocalization.Ring D w))

instance sourceNormedCommRing : NormedCommRing (Source D w ρ) where
  __ := sourceCommRing D w ρ
  __ := (show RingNorm (Source D w ρ) from
    InitialThetaWittRhoNorm.ringNorm D w ρ.val ρ.property.1.ne' ρ.property.2.le).toNormedRing

def sourceEquiv : InitialThetaBoundedWittLocalization.Ring D w ≃+* Source D w ρ :=
  RingEquiv.refl _

theorem source_norm (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ‖sourceEquiv D w ρ x‖ = InitialThetaWittRhoNorm.realValue D w ρ.val x := rfl

instance sourceNormOne : NormOneClass (Source D w ρ) :=
  ⟨InitialThetaWittRhoNorm.ringNorm_one D w ρ.val ρ.property.1.ne' ρ.property.2.le⟩

def Completed : Type u := UniformSpace.Completion (Source D w ρ)

instance completedNormedCommRing : NormedCommRing (Completed D w ρ) :=
  inferInstanceAs (NormedCommRing (UniformSpace.Completion (Source D w ρ)))

instance completedComplete : CompleteSpace (Completed D w ρ) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (Source D w ρ)))

def inclusion : InitialThetaBoundedWittLocalization.Ring D w →+* Completed D w ρ :=
  UniformSpace.Completion.coeRingHom.comp (sourceEquiv D w ρ).toRingHom

theorem inclusion_injective : Function.Injective (inclusion D w ρ) :=
  (UniformSpace.Completion.coe_injective (Source D w ρ)).comp (sourceEquiv D w ρ).injective

theorem inclusion_denseRange : DenseRange (inclusion D w ρ) :=
  (UniformSpace.Completion.denseRange_coe).comp
    (sourceEquiv D w ρ).surjective.denseRange (UniformSpace.Completion.continuous_coe (Source D w ρ))

theorem inclusion_norm (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ‖inclusion D w ρ x‖ = InitialThetaWittRhoNorm.realValue D w ρ.val x :=
  (UniformSpace.Completion.norm_coe (sourceEquiv D w ρ x)).trans (source_norm D w ρ x)

theorem inclusion_prime_norm :
    ‖inclusion D w ρ (Arithmetic.residueChar w.1)‖ = ρ.val.toReal := by
  rw [inclusion_norm]
  exact InitialThetaWittRhoNorm.ringNorm_prime D w ρ.val ρ.property.1.ne' ρ.property.2.le

theorem source_prime_norm : ‖(Arithmetic.residueChar w.1 : Source D w ρ)‖ = ρ.val.toReal :=
  InitialThetaWittRhoNorm.ringNorm_prime D w ρ.val ρ.property.1.ne' ρ.property.2.le

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoCompletion
