import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRadiusFaithfulness
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-IDEAL-CLOSED
source: Joshi II `se:ff-rings`, multiplicative rho norms on the actual
Frechet period ring and closedness of principal ideals.
fidelity: multiplication by any nonzero original common-ring element
is a uniform closed embedding, using exact multiplicative coordinate
norms and their faithfulness. Hence every principal ideal in this same
complete ring is closed. No division or kernel identity is assumed.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; original carrier, uniformity and norms are
retained. The theta-kernel and full eigen kernel remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalIdealClosed

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance commonIsUniformAddGroup : IsUniformAddGroup (Carrier D w) :=
  (commonSubring D w).toAddSubgroup.isUniformAddGroup

def multiplication (a : Carrier D w) : Carrier D w →+ Carrier D w where
  toFun x := a * x
  map_zero' := mul_zero a
  map_add' x y := mul_add a x y

theorem multiplication_continuous (a : Carrier D w) : Continuous (multiplication D w a) :=
  continuous_const.mul continuous_id

theorem tendsto_iff_multiplication (a : Carrier D w) (ha : a ≠ 0)
    {ι : Type*} (l : Filter ι) (f : ι → Carrier D w) (x : Carrier D w) :
    Filter.Tendsto f l (𝓝 x) ↔
      Filter.Tendsto (fun i => multiplication D w a (f i)) l (𝓝 (multiplication D w a x)) := by
  constructor
  · exact fun h => ((multiplication_continuous D w a).tendsto x).comp h
  · intro h
    have hs : Filter.Tendsto (fun i => a * (f i - x)) l (𝓝 0) := by
      have hs0 := h.sub_const (multiplication D w a x)
      change Filter.Tendsto (fun i => a * f i - a * x) l (𝓝 (a * x - a * x)) at hs0
      simpa only [← mul_sub, sub_self] using hs0
    apply tendsto_sub_nhds_zero_iff.mp
    apply (tendsto_iff_coordinates D w _ _ _).mpr
    intro ρ
    rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
    change Filter.Tendsto (fun i => coordinateSeminorm D w ρ (f i - x)) l (𝓝 0)
    have haρ : coordinateSeminorm D w ρ a ≠ 0 := fun hzero =>
      ha ((InitialThetaWittRadiusFaithfulness.coordinateSeminorm_eq_zero_iff D w ρ a).mp hzero)
    have ht := ((coordinateSeminorm_continuous D w ρ).tendsto 0).comp hs
    simp only [Function.comp_def, map_zero,
      InitialThetaWittMultiplicativeNorm.coordinateSeminorm_mul] at ht
    have hd := ht.div_const (coordinateSeminorm D w ρ a)
    simpa only [mul_div_cancel_left₀ _ haρ, zero_div] using hd

theorem multiplication_isInducing (a : Carrier D w) (ha : a ≠ 0) :
    Topology.IsInducing (multiplication D w a) := by
  apply Topology.isInducing_iff_nhds.mpr
  intro x
  apply le_antisymm
  · exact ((multiplication_continuous D w a).tendsto x).le_comap
  · have h := (tendsto_iff_multiplication D w a ha
      (Filter.comap (multiplication D w a) (𝓝 (multiplication D w a x))) id x).mpr Filter.tendsto_comap
    exact Filter.tendsto_id'.mp h

theorem multiplication_isUniformEmbedding (a : Carrier D w) (ha : a ≠ 0) :
    IsUniformEmbedding (multiplication D w a) :=
  AddMonoidHom.isUniformEmbedding_of_isEmbedding (multiplication_isInducing D w a ha).isEmbedding

theorem multiplication_isClosedEmbedding (a : Carrier D w) (ha : a ≠ 0) :
    Topology.IsClosedEmbedding (multiplication D w a) :=
  (multiplication_isUniformEmbedding D w a ha).isClosedEmbedding

theorem principalIdeal_eq_range (a : Carrier D w) :
    (Ideal.span {a} : Set (Carrier D w)) = Set.range (multiplication D w a) := by
  ext x
  change x ∈ (Ideal.span {a} : Ideal (Carrier D w)) ↔ _
  rw [Ideal.mem_span_singleton]
  change (∃ c, x = a * c) ↔ ∃ c, a * c = x
  exact exists_congr (fun c => eq_comm)

theorem principalIdeal_isClosed (a : Carrier D w) : IsClosed (Ideal.span {a} : Set (Carrier D w)) := by
  by_cases ha : a = 0
  · subst a
    rw [Ideal.span_singleton_zero]
    exact (isClosed_singleton : IsClosed ({0} : Set (Carrier D w)))
  · rw [principalIdeal_eq_range]
    exact (multiplication_isClosedEmbedding D w a ha).isClosed_range

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalIdealClosed
