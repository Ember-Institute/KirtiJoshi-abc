import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalRadiusTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittMultiplicativeNorm
import Mathlib.Topology.Algebra.UniformRing

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-COMPARISON
source: Joshi II `se:ff-rings`, the all-radius completion defining the
period ring used by `pr:teichmuller-lift-A/B`.
fidelity: canonically identifies the Hausdorff completion of the actual
bounded Witt ring with its proved all-radius uniformity and the existing
diagonal-closure ring. The comparison is both a uniform equivalence and
a ring equivalence, fixes the original ring, and preserves its actual
rho norms. Proves the corresponding extension and uniqueness property
for complete Hausdorff topological target rings.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; normalized Q_p seminorms and full paper
period/BK comparisons remain separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetComparison

open JoshiTeich.Prologue InitialThetaWittFrechetSource
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Completed := UniformSpace.Completion (Source D w)
abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w

instance carrierUniformAddGroup : IsUniformAddGroup (Carrier D w) :=
  IsUniformInducing.isUniformAddGroup
    (InitialThetaWittAllRadiusCompletion.commonSubring D w).subtype.toAddMonoidHom
    isUniformEmbedding_subtype_val.isUniformInducing

theorem source_tendsto_iff_norms {ι : Type*} (l : Filter ι) (f : ι → Source D w) (x : Source D w) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : InitialThetaWittRhoCompletion.Radius,
      Filter.Tendsto
        (fun i => InitialThetaWittRhoNorm.realValue D w ρ.val
          ((sourceEquiv D w).symm (f i) - (sourceEquiv D w).symm x)) l (𝓝 0) := by
  rw [InitialThetaWittFrechetSource.tendsto_iff_radii]
  apply forall_congr'
  intro ρ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [← map_sub, InitialThetaWittRhoCompletion.inclusion_norm]

def uniformEquiv : Completed D w ≃ᵤ Carrier D w :=
  (UniformSpace.Completion.cPkg (α := Source D w)).compareEquiv (completionPackage D w)

theorem uniformEquiv_coe (x : Source D w) :
    uniformEquiv D w (x : Completed D w) = toCarrier D w x :=
  (UniformSpace.Completion.cPkg (α := Source D w)).compare_coe (completionPackage D w) x

def comparisonHom : Completed D w →+* Carrier D w :=
  UniformSpace.Completion.extensionHom (toCarrier D w) (toCarrier_continuous D w)

theorem comparisonHom_continuous : Continuous (comparisonHom D w) :=
  UniformSpace.Completion.continuous_extension

theorem comparisonHom_coe (x : Source D w) : comparisonHom D w (x : Completed D w) = toCarrier D w x :=
  UniformSpace.Completion.extensionHom_coe (toCarrier D w) (toCarrier_continuous D w) x

theorem comparisonHom_eq_uniformEquiv (x : Completed D w) :
    comparisonHom D w x = uniformEquiv D w x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (comparisonHom_continuous D w) (uniformEquiv D w).continuous) ?_
  intro a
  rw [comparisonHom_coe, uniformEquiv_coe]

def ringEquiv : Completed D w ≃+* Carrier D w where
  __ := (uniformEquiv D w).toEquiv
  map_add' x y := by
    change uniformEquiv D w (x + y) = uniformEquiv D w x + uniformEquiv D w y
    rw [← comparisonHom_eq_uniformEquiv, ← comparisonHom_eq_uniformEquiv,
      ← comparisonHom_eq_uniformEquiv, map_add]
  map_mul' x y := by
    change uniformEquiv D w (x * y) = uniformEquiv D w x * uniformEquiv D w y
    rw [← comparisonHom_eq_uniformEquiv, ← comparisonHom_eq_uniformEquiv,
      ← comparisonHom_eq_uniformEquiv, map_mul]

theorem ringEquiv_continuous : Continuous (ringEquiv D w) := (uniformEquiv D w).continuous

theorem ringEquiv_symm_continuous : Continuous (ringEquiv D w).symm := (uniformEquiv D w).continuous_symm

theorem ringEquiv_coe (x : Source D w) : ringEquiv D w (x : Completed D w) = toCarrier D w x :=
  uniformEquiv_coe D w x

theorem ringEquiv_symm_toCarrier (x : Source D w) :
    (ringEquiv D w).symm (toCarrier D w x) = (x : Completed D w) := by
  apply (ringEquiv D w).injective
  rw [RingEquiv.apply_symm_apply, ringEquiv_coe]

instance completedMetrizable : TopologicalSpace.MetrizableSpace (Completed D w) :=
  (uniformEquiv D w).toHomeomorph.isEmbedding.metrizableSpace

def originalInclusion : InitialThetaBoundedWittLocalization.Ring D w →+* Completed D w :=
  UniformSpace.Completion.coeRingHom.comp (sourceEquiv D w).toRingHom

theorem ringEquiv_originalInclusion (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ringEquiv D w (originalInclusion D w x) = InitialThetaWittAllRadiusCompletion.inclusion D w x :=
  ringEquiv_coe D w (sourceEquiv D w x)

def radiusMap (ρ : InitialThetaWittRhoCompletion.Radius) :
    Completed D w →+* InitialThetaWittRhoCompletion.Completed D w ρ :=
  (InitialThetaWittAllRadiusCompletion.evaluate D w ρ).comp (ringEquiv D w).toRingHom

theorem radiusMap_continuous (ρ : InitialThetaWittRhoCompletion.Radius) : Continuous (radiusMap D w ρ) :=
  (InitialThetaWittAllRadiusCompletion.evaluate_continuous D w ρ).comp (ringEquiv_continuous D w)

theorem radiusMap_originalInclusion (ρ : InitialThetaWittRhoCompletion.Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    radiusMap D w ρ (originalInclusion D w x) = InitialThetaWittRhoCompletion.inclusion D w ρ x := by
  change InitialThetaWittAllRadiusCompletion.evaluate D w ρ
    (ringEquiv D w (originalInclusion D w x)) = _
  rw [ringEquiv_originalInclusion, InitialThetaWittAllRadiusCompletion.evaluate_inclusion]

theorem norm_radiusMap_originalInclusion (ρ : InitialThetaWittRhoCompletion.Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ‖radiusMap D w ρ (originalInclusion D w x)‖ = InitialThetaWittRhoNorm.realValue D w ρ.val x := by
  rw [radiusMap_originalInclusion, InitialThetaWittRhoCompletion.inclusion_norm]

theorem norm_radiusMap_mul (ρ : InitialThetaWittRhoCompletion.Radius) (x y : Completed D w) :
    ‖radiusMap D w ρ (x * y)‖ = ‖radiusMap D w ρ x‖ * ‖radiusMap D w ρ y‖ := by
  rw [map_mul, norm_mul]

theorem tendsto_iff_radiusMaps {ι : Type*} (l : Filter ι) (f : ι → Completed D w) (x : Completed D w) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : InitialThetaWittRhoCompletion.Radius,
      Filter.Tendsto (fun i => radiusMap D w ρ (f i)) l (𝓝 (radiusMap D w ρ x)) := by
  rw [(uniformEquiv D w).toHomeomorph.isInducing.tendsto_nhds_iff,
    InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates]
  rfl

section Universal
variable {R : Type*} [UniformSpace R] [Ring R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [CompleteSpace R] [T0Space R]

def extendHom (f : Source D w →+* R) (hf : Continuous f) : Carrier D w →+* R :=
  (UniformSpace.Completion.extensionHom f hf).comp (ringEquiv D w).symm.toRingHom

theorem extendHom_continuous (f : Source D w →+* R) (hf : Continuous f) :
    Continuous (extendHom D w f hf) :=
  UniformSpace.Completion.continuous_extension.comp (ringEquiv_symm_continuous D w)

theorem extendHom_toCarrier (f : Source D w →+* R) (hf : Continuous f) (x : Source D w) :
    extendHom D w f hf (toCarrier D w x) = f x := by
  change UniformSpace.Completion.extensionHom f hf ((ringEquiv D w).symm (toCarrier D w x)) = f x
  rw [ringEquiv_symm_toCarrier, UniformSpace.Completion.extensionHom_coe]

theorem extendHom_unique (f : Source D w →+* R) (hf : Continuous f) (g : Carrier D w →+* R)
    (hg : Continuous g) (h : ∀ x : Source D w, g (toCarrier D w x) = f x) :
    g = extendHom D w f hf := by
  apply RingHom.ext
  intro y
  refine (toCarrier_denseRange D w).induction_on y
    (isClosed_eq hg (extendHom_continuous D w f hf)) ?_
  intro x
  rw [h, extendHom_toCarrier]

end Universal
end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetComparison
