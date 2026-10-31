import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetComparison
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-RHO-SEMINORM
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`.
fidelity: defines the actual-derived family of rho seminorms on the
Frechet completion by composing the existing radius maps with the target
norm.  It records multiplication, continuity, agreement with the original
rho values on the bounded localization, separation by the full radius
family, and the already established radius-map convergence criterion.
boundary: Scene1/Derived; this does not identify the carrier with paper `B`,
does not define the paper's rho norm, and does not supply H1e/BK or a
holomorphoid comparison.  Original proofs; no reference implementation
copied.  Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoSeminorm

open JoshiTeich.Prologue
open InitialThetaWittFrechetComparison
open InitialThetaWittAllRadiusCompletion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Radius := InitialThetaWittRhoCompletion.Radius
abbrev Completed := InitialThetaWittFrechetComparison.Completed D w

/-- The actual rho seminorm obtained from the corresponding radius map. -/
def frechetRhoSeminorm (ρ : Radius) : RingSeminorm (Completed D w) where
  toFun x := ‖radiusMap D w ρ x‖
  map_zero' := by rw [map_zero, norm_zero]
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by rw [map_neg, norm_neg]
  mul_le' x y := by rw [map_mul]; exact norm_mul_le _ _

theorem frechetRhoSeminorm_apply (ρ : Radius) (x : Completed D w) :
    frechetRhoSeminorm D w ρ x = ‖radiusMap D w ρ x‖ := rfl

theorem frechetRhoSeminorm_continuous (ρ : Radius) :
    Continuous (frechetRhoSeminorm D w ρ) :=
  (radiusMap_continuous D w ρ).norm

theorem frechetRhoSeminorm_mul (ρ : Radius) (x y : Completed D w) :
    frechetRhoSeminorm D w ρ (x * y) =
      frechetRhoSeminorm D w ρ x * frechetRhoSeminorm D w ρ y := by
  exact norm_radiusMap_mul D w ρ x y

theorem frechetRhoSeminorm_originalInclusion (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    frechetRhoSeminorm D w ρ (originalInclusion D w x) =
      InitialThetaWittRhoNorm.realValue D w ρ.val x := by
  exact norm_radiusMap_originalInclusion D w ρ x

theorem frechetRhoSeminorm_prime (ρ : Radius) :
    frechetRhoSeminorm D w ρ
        (originalInclusion D w (Arithmetic.residueChar w.1)) = ρ.val.toReal := by
  rw [frechetRhoSeminorm_originalInclusion]
  exact InitialThetaWittRhoNorm.ringNorm_prime D w ρ.val
    ρ.property.1.ne' ρ.property.2.le

theorem frechetRhoSeminorms_separate_zero (x : Completed D w) :
    (∀ ρ : Radius, frechetRhoSeminorm D w ρ x = 0) ↔ x = 0 := by
  constructor
  · intro hx
    apply (ringEquiv D w).injective
    apply InitialThetaWittAllRadiusCompletion.ext D w
    intro ρ
    have hnorm : ‖evaluate D w ρ ((ringEquiv D w) x)‖ = 0 := by
      change frechetRhoSeminorm D w ρ x = 0
      exact hx ρ
    have hzero : evaluate D w ρ ((ringEquiv D w) x) = 0 := norm_eq_zero.mp hnorm
    simp [hzero]
  · rintro rfl
    intro ρ
    exact map_zero _

theorem tendsto_iff_radiusMaps_frechetRhoSeminorm {ι : Type*} (l : Filter ι)
    (f : ι → Completed D w) (x : Completed D w) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : Radius,
      Filter.Tendsto (fun i => radiusMap D w ρ (f i)) l
        (𝓝 (radiusMap D w ρ x)) :=
  tendsto_iff_radiusMaps D w l f x

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetRhoSeminorm
