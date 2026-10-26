import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusCompletion
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-SOURCE
source: Joshi II `se:ff-rings`, completion of the bounded Witt period
ring for the entire family of rho norms in `pr:teichmuller-lift-A/B`.
fidelity: equips a separate copy of the original bounded Witt ring with
the uniform structure induced by its original maps into all radius
completions. Proves the compatible ring and uniform additive group laws,
separation, and that the existing common ring is an abstract completion
of this actual source. No topology is supplied as a mathematical input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the completion comparison and paper period/BK
identities remain separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetSource

open JoshiTeich.Prologue
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def Source : Type u := InitialThetaBoundedWittLocalization.Ring D w

instance sourceCommRing : CommRing (Source D w) :=
  inferInstanceAs (CommRing (InitialThetaBoundedWittLocalization.Ring D w))

def sourceEquiv : InitialThetaBoundedWittLocalization.Ring D w ≃+* Source D w := RingEquiv.refl _

def toProduct : Source D w →+* InitialThetaWittAllRadiusCompletion.Product D w :=
  (InitialThetaWittAllRadiusCompletion.diagonal D w).comp (sourceEquiv D w).symm.toRingHom

def toCarrier : Source D w →+* InitialThetaWittAllRadiusCompletion.Carrier D w :=
  (InitialThetaWittAllRadiusCompletion.inclusion D w).comp (sourceEquiv D w).symm.toRingHom

instance sourceUniformSpace : UniformSpace (Source D w) :=
  UniformSpace.comap (toProduct D w) inferInstance

theorem toProduct_isUniformInducing : IsUniformInducing (toProduct D w) := ⟨rfl⟩

theorem toProduct_injective : Function.Injective (toProduct D w) := by
  let ρ : InitialThetaWittRhoCompletion.Radius :=
    ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  intro x y h
  apply (sourceEquiv D w).symm.injective
  apply InitialThetaWittRhoCompletion.inclusion_injective D w ρ
  exact congrFun h ρ

theorem toProduct_isUniformEmbedding : IsUniformEmbedding (toProduct D w) :=
  ⟨toProduct_isUniformInducing D w, toProduct_injective D w⟩

instance sourceT2Space : T2Space (Source D w) :=
  (toProduct_isUniformEmbedding D w).isEmbedding.t2Space

instance sourceUniformAddGroup : IsUniformAddGroup (Source D w) :=
  IsUniformInducing.isUniformAddGroup (toProduct D w).toAddMonoidHom (toProduct_isUniformInducing D w)

instance sourceTopologicalRing : IsTopologicalRing (Source D w) where
  continuous_add := by
    apply (toProduct_isUniformInducing D w).isInducing.continuous_iff.mpr
    have h := (toProduct_isUniformInducing D w).uniformContinuous.continuous
    simpa only [Function.comp_def, map_add] using
      continuous_add.comp ((h.comp continuous_fst).prodMk (h.comp continuous_snd))
  continuous_mul := by
    apply (toProduct_isUniformInducing D w).isInducing.continuous_iff.mpr
    have h := (toProduct_isUniformInducing D w).uniformContinuous.continuous
    simpa only [Function.comp_def, map_mul] using
      continuous_mul.comp ((h.comp continuous_fst).prodMk (h.comp continuous_snd))
  continuous_neg := by
    apply (toProduct_isUniformInducing D w).isInducing.continuous_iff.mpr
    simpa only [Function.comp_def, map_neg] using
      continuous_neg.comp (toProduct_isUniformInducing D w).uniformContinuous.continuous

theorem toCarrier_isUniformInducing : IsUniformInducing (toCarrier D w) := by
  have h : IsUniformInducing (fun x : InitialThetaWittAllRadiusCompletion.Carrier D w =>
      (x : InitialThetaWittAllRadiusCompletion.Product D w)) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  exact h.of_comp_iff.mp (toProduct_isUniformInducing D w)

theorem toCarrier_denseRange : DenseRange (toCarrier D w) :=
  InitialThetaWittAllRadiusCompletion.inclusion_denseRange D w

theorem toCarrier_continuous : Continuous (toCarrier D w) :=
  (toCarrier_isUniformInducing D w).uniformContinuous.continuous

theorem toCarrier_sourceEquiv (x : InitialThetaBoundedWittLocalization.Ring D w) :
    toCarrier D w (sourceEquiv D w x) = InitialThetaWittAllRadiusCompletion.inclusion D w x := rfl

theorem evaluate_toCarrier (ρ : InitialThetaWittRhoCompletion.Radius) (x : Source D w) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (toCarrier D w x) =
      InitialThetaWittRhoCompletion.inclusion D w ρ ((sourceEquiv D w).symm x) := rfl

theorem tendsto_iff_radii {ι : Type*} (l : Filter ι) (f : ι → Source D w) (x : Source D w) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : InitialThetaWittRhoCompletion.Radius,
      Filter.Tendsto
        (fun i => InitialThetaWittRhoCompletion.inclusion D w ρ ((sourceEquiv D w).symm (f i))) l
        (𝓝 (InitialThetaWittRhoCompletion.inclusion D w ρ ((sourceEquiv D w).symm x))) := by
  rw [(toProduct_isUniformInducing D w).isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

def completionPackage : AbstractCompletion (Source D w) where
  space := InitialThetaWittAllRadiusCompletion.Carrier D w
  coe := toCarrier D w
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := toCarrier_isUniformInducing D w
  dense := toCarrier_denseRange D w

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetSource
