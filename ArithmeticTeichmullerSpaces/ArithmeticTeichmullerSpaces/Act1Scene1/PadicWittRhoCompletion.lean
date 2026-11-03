import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoNorm
import Mathlib.Analysis.Normed.Module.Completion

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RHO-COMPLETION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, completion
of the standard bounded period ring at a fixed rho in (0,1).
fidelity: puts the original standard rho norm on a separate copy of the
p-only bounded Witt localization and forms its Hausdorff normed-ring
completion. The original ring has an injective dense inclusion preserving
that norm. All declarations use only p and the radius.
Original proofs using the project's actual completion construction;
no reference implementation copied. Prologue R5 unchanged.
boundary: this is a fixed-radius completion; the common Frechet ring and
paper B/period/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoCompletion

open scoped ENNReal Topology
noncomputable section
variable (p : ℕ) [Fact p.Prime]

abbrev Radius := {ρ : ℝ≥0∞ // 0 < ρ ∧ ρ < 1}

/-- A separate copy allows each radius its own norm and uniform structure. -/
def Source (_ρ : Radius) : Type := PadicBoundedWittLocalization.Ring p

variable (ρ : Radius)

instance sourceCommRing : CommRing (Source p ρ) :=
  inferInstanceAs (CommRing (PadicBoundedWittLocalization.Ring p))

instance sourceNormedCommRing : NormedCommRing (Source p ρ) where
  __ := sourceCommRing p ρ
  __ := (show RingNorm (Source p ρ) from
    PadicWittRhoNorm.ringNorm p ρ.val ρ.property.1.ne' ρ.property.2.le).toNormedRing

def sourceEquiv : PadicBoundedWittLocalization.Ring p ≃+* Source p ρ :=
  RingEquiv.refl _

theorem source_norm (x : PadicBoundedWittLocalization.Ring p) :
    ‖sourceEquiv p ρ x‖ = PadicWittRhoNorm.realValue p ρ.val x := rfl

instance sourceNormOne : NormOneClass (Source p ρ) :=
  ⟨PadicWittRhoNorm.ringNorm_one p ρ.val ρ.property.1.ne' ρ.property.2.le⟩

def Completed : Type := UniformSpace.Completion (Source p ρ)

instance completedNormedCommRing : NormedCommRing (Completed p ρ) :=
  inferInstanceAs (NormedCommRing (UniformSpace.Completion (Source p ρ)))

instance completedComplete : CompleteSpace (Completed p ρ) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (Source p ρ)))

def inclusion : PadicBoundedWittLocalization.Ring p →+* Completed p ρ :=
  UniformSpace.Completion.coeRingHom.comp (sourceEquiv p ρ).toRingHom

theorem inclusion_injective : Function.Injective (inclusion p ρ) :=
  (UniformSpace.Completion.coe_injective (Source p ρ)).comp (sourceEquiv p ρ).injective

theorem inclusion_denseRange : DenseRange (inclusion p ρ) :=
  (UniformSpace.Completion.denseRange_coe).comp
    (sourceEquiv p ρ).surjective.denseRange (UniformSpace.Completion.continuous_coe (Source p ρ))

theorem inclusion_norm (x : PadicBoundedWittLocalization.Ring p) :
    ‖inclusion p ρ x‖ = PadicWittRhoNorm.realValue p ρ.val x :=
  (UniformSpace.Completion.norm_coe (sourceEquiv p ρ x)).trans (source_norm p ρ x)

theorem inclusion_prime_norm :
    ‖inclusion p ρ (p)‖ = ρ.val.toReal := by
  rw [inclusion_norm]
  exact PadicWittRhoNorm.ringNorm_prime p ρ.val ρ.property.1.ne' ρ.property.2.le

theorem source_prime_norm : ‖(p : Source p ρ)‖ = ρ.val.toReal :=
  PadicWittRhoNorm.ringNorm_prime p ρ.val ρ.property.1.ne' ρ.property.2.le

end
end JoshiTeich.Act1Scene1.PadicWittRhoCompletion
