import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusCompletion
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FRECHET-SOURCE
source: Joshi II `se:ff-rings`, completion of the bounded Witt period
ring for the entire family of rho norms in `pr:teichmuller-lift-A/B`.
fidelity: equips a separate copy of the original bounded Witt ring with
the uniform structure induced by its original maps into all radius
completions. Proves the compatible ring and uniform additive group laws,
separation, and that the existing common ring is an abstract completion
of this independent standard source. Only p and its primality instance enter
the construction. No topology is supplied as a mathematical input.
Original proofs using the project's actual all-radius source construction;
no reference implementation copied.
boundary: Scene1/Derived; the completion comparison, metrizability,
scalar/Frobenius and paper period/BK identities remain separate obligations.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittFrechetSource

open scoped Topology
noncomputable section
variable (p : ℕ) [Fact p.Prime]

def Source : Type := PadicBoundedWittLocalization.Ring p

instance sourceCommRing : CommRing (Source p) :=
  inferInstanceAs (CommRing (PadicBoundedWittLocalization.Ring p))

def sourceEquiv : PadicBoundedWittLocalization.Ring p ≃+* Source p := RingEquiv.refl _

def toProduct : Source p →+* PadicWittAllRadiusCompletion.Product p :=
  (PadicWittAllRadiusCompletion.diagonal p).comp (sourceEquiv p).symm.toRingHom

def toCarrier : Source p →+* PadicWittAllRadiusCompletion.Carrier p :=
  (PadicWittAllRadiusCompletion.inclusion p).comp (sourceEquiv p).symm.toRingHom

instance sourceUniformSpace : UniformSpace (Source p) :=
  UniformSpace.comap (toProduct p) inferInstance

theorem toProduct_isUniformInducing : IsUniformInducing (toProduct p) := ⟨rfl⟩

theorem toProduct_injective : Function.Injective (toProduct p) := by
  let ρ : PadicWittRhoCompletion.Radius :=
    ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  intro x y h
  apply (sourceEquiv p).symm.injective
  apply PadicWittRhoCompletion.inclusion_injective p ρ
  exact congrFun h ρ

theorem toProduct_isUniformEmbedding : IsUniformEmbedding (toProduct p) :=
  ⟨toProduct_isUniformInducing p, toProduct_injective p⟩

instance sourceT2Space : T2Space (Source p) :=
  (toProduct_isUniformEmbedding p).isEmbedding.t2Space

instance sourceUniformAddGroup : IsUniformAddGroup (Source p) :=
  IsUniformInducing.isUniformAddGroup (toProduct p).toAddMonoidHom (toProduct_isUniformInducing p)

instance sourceTopologicalRing : IsTopologicalRing (Source p) where
  continuous_add := by
    apply (toProduct_isUniformInducing p).isInducing.continuous_iff.mpr
    have h := (toProduct_isUniformInducing p).uniformContinuous.continuous
    simpa only [Function.comp_def, map_add] using
      continuous_add.comp ((h.comp continuous_fst).prodMk (h.comp continuous_snd))
  continuous_mul := by
    apply (toProduct_isUniformInducing p).isInducing.continuous_iff.mpr
    have h := (toProduct_isUniformInducing p).uniformContinuous.continuous
    simpa only [Function.comp_def, map_mul] using
      continuous_mul.comp ((h.comp continuous_fst).prodMk (h.comp continuous_snd))
  continuous_neg := by
    apply (toProduct_isUniformInducing p).isInducing.continuous_iff.mpr
    simpa only [Function.comp_def, map_neg] using
      continuous_neg.comp (toProduct_isUniformInducing p).uniformContinuous.continuous

theorem toCarrier_isUniformInducing : IsUniformInducing (toCarrier p) := by
  have h : IsUniformInducing (fun x : PadicWittAllRadiusCompletion.Carrier p =>
      (x : PadicWittAllRadiusCompletion.Product p)) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  exact h.of_comp_iff.mp (toProduct_isUniformInducing p)

theorem toCarrier_denseRange : DenseRange (toCarrier p) :=
  PadicWittAllRadiusCompletion.inclusion_denseRange p

theorem toCarrier_continuous : Continuous (toCarrier p) :=
  (toCarrier_isUniformInducing p).uniformContinuous.continuous

theorem toCarrier_sourceEquiv (x : PadicBoundedWittLocalization.Ring p) :
    toCarrier p (sourceEquiv p x) = PadicWittAllRadiusCompletion.inclusion p x := rfl

theorem evaluate_toCarrier (ρ : PadicWittRhoCompletion.Radius) (x : Source p) :
    PadicWittAllRadiusCompletion.evaluate p ρ (toCarrier p x) =
      PadicWittRhoCompletion.inclusion p ρ ((sourceEquiv p).symm x) := rfl

theorem tendsto_iff_radii {ι : Type*} (l : Filter ι) (f : ι → Source p) (x : Source p) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : PadicWittRhoCompletion.Radius,
      Filter.Tendsto
        (fun i => PadicWittRhoCompletion.inclusion p ρ ((sourceEquiv p).symm (f i))) l
        (𝓝 (PadicWittRhoCompletion.inclusion p ρ ((sourceEquiv p).symm x))) := by
  rw [(toProduct_isUniformInducing p).isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

def completionPackage : AbstractCompletion (Source p) where
  space := PadicWittAllRadiusCompletion.Carrier p
  coe := toCarrier p
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := toCarrier_isUniformInducing p
  dense := toCarrier_denseRange p

end
end JoshiTeich.Act1Scene1.PadicWittFrechetSource
