import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrechetSource
import Mathlib.Topology.Algebra.UniformRing

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FRECHET-COMPARISON
source: Joshi II `se:ff-rings`, the all-radius completion defining the
period ring used by `pr:teichmuller-lift-A/B`.
fidelity: canonically identifies the Hausdorff completion of the independent standard
bounded Witt ring with its proved all-radius uniformity and the existing
diagonal-closure ring. The comparison is both a uniform equivalence and
a ring equivalence, fixes the original ring, and preserves its standard
rho norms. Only p and its primality instance enter the construction.
Proves the corresponding extension and uniqueness property
for complete Hausdorff topological target rings.
Original proofs using the project's actual completion comparison pattern;
no reference implementation copied.
boundary: Scene1/Derived; metrizability, multiplicative norm equality,
scalar/Frobenius transport and paper period/BK comparisons remain separate.
No actual InitialThetaData parameter is used. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittFrechetComparison

open PadicWittFrechetSource
open scoped Topology
noncomputable section
variable (p : ℕ) [Fact p.Prime]

abbrev Completed := UniformSpace.Completion (Source p)
abbrev Carrier := PadicWittAllRadiusCompletion.Carrier p

instance carrierUniformAddGroup : IsUniformAddGroup (Carrier p) :=
  IsUniformInducing.isUniformAddGroup
    (PadicWittAllRadiusCompletion.commonSubring p).subtype.toAddMonoidHom
    isUniformEmbedding_subtype_val.isUniformInducing

theorem source_tendsto_iff_norms {ι : Type*} (l : Filter ι) (f : ι → Source p) (x : Source p) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : PadicWittRhoCompletion.Radius,
      Filter.Tendsto
        (fun i => PadicWittRhoNorm.realValue p ρ.val
          ((sourceEquiv p).symm (f i) - (sourceEquiv p).symm x)) l (𝓝 0) := by
  rw [PadicWittFrechetSource.tendsto_iff_radii]
  apply forall_congr'
  intro ρ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [← map_sub, PadicWittRhoCompletion.inclusion_norm]

def uniformEquiv : Completed p ≃ᵤ Carrier p :=
  (UniformSpace.Completion.cPkg (α := Source p)).compareEquiv (completionPackage p)

theorem uniformEquiv_coe (x : Source p) :
    uniformEquiv p (x : Completed p) = toCarrier p x :=
  (UniformSpace.Completion.cPkg (α := Source p)).compare_coe (completionPackage p) x

def comparisonHom : Completed p →+* Carrier p :=
  UniformSpace.Completion.extensionHom (toCarrier p) (toCarrier_continuous p)

theorem comparisonHom_continuous : Continuous (comparisonHom p) :=
  UniformSpace.Completion.continuous_extension

theorem comparisonHom_coe (x : Source p) : comparisonHom p (x : Completed p) = toCarrier p x :=
  UniformSpace.Completion.extensionHom_coe (toCarrier p) (toCarrier_continuous p) x

theorem comparisonHom_eq_uniformEquiv (x : Completed p) :
    comparisonHom p x = uniformEquiv p x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (comparisonHom_continuous p) (uniformEquiv p).continuous) ?_
  intro a
  rw [comparisonHom_coe, uniformEquiv_coe]

def ringEquiv : Completed p ≃+* Carrier p where
  __ := (uniformEquiv p).toEquiv
  map_add' x y := by
    change uniformEquiv p (x + y) = uniformEquiv p x + uniformEquiv p y
    rw [← comparisonHom_eq_uniformEquiv, ← comparisonHom_eq_uniformEquiv,
      ← comparisonHom_eq_uniformEquiv, map_add]
  map_mul' x y := by
    change uniformEquiv p (x * y) = uniformEquiv p x * uniformEquiv p y
    rw [← comparisonHom_eq_uniformEquiv, ← comparisonHom_eq_uniformEquiv,
      ← comparisonHom_eq_uniformEquiv, map_mul]

theorem ringEquiv_continuous : Continuous (ringEquiv p) := (uniformEquiv p).continuous

theorem ringEquiv_symm_continuous : Continuous (ringEquiv p).symm := (uniformEquiv p).continuous_symm

theorem ringEquiv_coe (x : Source p) : ringEquiv p (x : Completed p) = toCarrier p x :=
  uniformEquiv_coe p x

theorem ringEquiv_symm_toCarrier (x : Source p) :
    (ringEquiv p).symm (toCarrier p x) = (x : Completed p) := by
  apply (ringEquiv p).injective
  rw [RingEquiv.apply_symm_apply, ringEquiv_coe]

def originalInclusion : PadicBoundedWittLocalization.Ring p →+* Completed p :=
  UniformSpace.Completion.coeRingHom.comp (sourceEquiv p).toRingHom

theorem ringEquiv_originalInclusion (x : PadicBoundedWittLocalization.Ring p) :
    ringEquiv p (originalInclusion p x) = PadicWittAllRadiusCompletion.inclusion p x :=
  ringEquiv_coe p (sourceEquiv p x)

def radiusMap (ρ : PadicWittRhoCompletion.Radius) :
    Completed p →+* PadicWittRhoCompletion.Completed p ρ :=
  (PadicWittAllRadiusCompletion.evaluate p ρ).comp (ringEquiv p).toRingHom

theorem radiusMap_continuous (ρ : PadicWittRhoCompletion.Radius) : Continuous (radiusMap p ρ) :=
  (PadicWittAllRadiusCompletion.evaluate_continuous p ρ).comp (ringEquiv_continuous p)

theorem radiusMap_originalInclusion (ρ : PadicWittRhoCompletion.Radius)
    (x : PadicBoundedWittLocalization.Ring p) :
    radiusMap p ρ (originalInclusion p x) = PadicWittRhoCompletion.inclusion p ρ x := by
  change PadicWittAllRadiusCompletion.evaluate p ρ
    (ringEquiv p (originalInclusion p x)) = _
  rw [ringEquiv_originalInclusion, PadicWittAllRadiusCompletion.evaluate_inclusion]

theorem norm_radiusMap_originalInclusion (ρ : PadicWittRhoCompletion.Radius)
    (x : PadicBoundedWittLocalization.Ring p) :
    ‖radiusMap p ρ (originalInclusion p x)‖ = PadicWittRhoNorm.realValue p ρ.val x := by
  rw [radiusMap_originalInclusion, PadicWittRhoCompletion.inclusion_norm]

theorem tendsto_iff_radiusMaps {ι : Type*} (l : Filter ι) (f : ι → Completed p) (x : Completed p) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : PadicWittRhoCompletion.Radius,
      Filter.Tendsto (fun i => radiusMap p ρ (f i)) l (𝓝 (radiusMap p ρ x)) := by
  rw [(uniformEquiv p).toHomeomorph.isInducing.tendsto_nhds_iff,
    PadicWittAllRadiusCompletion.tendsto_iff_coordinates]
  rfl

section Universal
variable {R : Type*} [UniformSpace R] [Ring R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [CompleteSpace R] [T0Space R]

def extendHom (f : Source p →+* R) (hf : Continuous f) : Carrier p →+* R :=
  (UniformSpace.Completion.extensionHom f hf).comp (ringEquiv p).symm.toRingHom

theorem extendHom_continuous (f : Source p →+* R) (hf : Continuous f) :
    Continuous (extendHom p f hf) :=
  UniformSpace.Completion.continuous_extension.comp (ringEquiv_symm_continuous p)

theorem extendHom_toCarrier (f : Source p →+* R) (hf : Continuous f) (x : Source p) :
    extendHom p f hf (toCarrier p x) = f x := by
  change UniformSpace.Completion.extensionHom f hf ((ringEquiv p).symm (toCarrier p x)) = f x
  rw [ringEquiv_symm_toCarrier, UniformSpace.Completion.extensionHom_coe]

theorem extendHom_unique (f : Source p →+* R) (hf : Continuous f) (g : Carrier p →+* R)
    (hg : Continuous g) (h : ∀ x : Source p, g (toCarrier p x) = f x) :
    g = extendHom p f hf := by
  apply RingHom.ext
  intro y
  refine (toCarrier_denseRange p).induction_on y
    (isClosed_eq hg (extendHom_continuous p f hf)) ?_
  intro x
  rw [h, extendHom_toCarrier]

end Universal
end
end JoshiTeich.Act1Scene1.PadicWittFrechetComparison
