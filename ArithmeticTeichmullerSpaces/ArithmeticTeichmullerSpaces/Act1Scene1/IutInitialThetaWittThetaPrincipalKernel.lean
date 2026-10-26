import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalIdealClosed
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittBoundedThetaPrincipal
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalRadiusTopology
import Mathlib.Topology.Sequences

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-THETA-PRINCIPAL-KERNEL
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, the original untilt evaluation kernel.
fidelity: proves ker(theta)=(xi) in the entire original common complete
ring, for the actual image of [p-flat]-p. Corrects dense original bounded
approximations by actual Teichmuller lifts that tend to zero at all
radii. The corrected terms lie in the proved source principal kernel;
closedness of multiplication by xi gives the completed kernel identity.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no source or completed principal-kernel law
is input. The full phi=p kernel versus the Tate line remains open.
Original topology and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittThetaPrincipalKernel

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittThetaEvaluation InitialThetaWittThetaBound
open InitialThetaWittBoundedThetaPrincipal InitialThetaWittPrincipalIdealClosed
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def primitive : Carrier D w :=
  InitialThetaWittAllRadiusExpansion.ainfMap D w (InitialThetaTiltFontaine.primitive D w)

theorem inclusion_boundedPrimitive : inclusion D w (boundedPrimitive D w) = primitive D w := rfl

theorem primitive_ne_zero : primitive D w ≠ 0 := by
  intro h
  apply InitialThetaTiltFontaine.primitive_ne_zero D w
  apply InitialThetaBoundedWittLocalization.inclusion_injective D w
  apply inclusion_injective D w
  change inclusion D w (boundedPrimitive D w) =
    inclusion D w (InitialThetaBoundedWittLocalization.inclusion D w 0)
  simpa only [inclusion_boundedPrimitive, map_zero] using h

theorem evaluation_primitive : evaluation D w (primitive D w) = 0 := by
  rw [← inclusion_boundedPrimitive, evaluation_inclusion, boundedPrimitive_evaluation]

theorem corrected_mem_span (a : InitialThetaBoundedWittLocalization.Ring D w)
    (ha : ‖InitialThetaBoundedWittLocalization.evaluation D w a‖ ≤ 1) :
    inclusion D w (corrected D w a) ∈ (Ideal.span {primitive D w} : Ideal (Carrier D w)) := by
  apply Ideal.mem_span_singleton.mpr
  have h := map_dvd (inclusion D w)
    ((bounded_evaluation_eq_zero_iff_dvd D w (corrected D w a)).mp (corrected_evaluation D w a ha))
  rwa [inclusion_boundedPrimitive] at h

theorem mem_span_of_evaluation_eq_zero (x : Carrier D w) (hx : evaluation D w x = 0) :
    x ∈ (Ideal.span {primitive D w} : Ideal (Carrier D w)) := by
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp (inclusion_denseRange D w x)
  choose a ha using hv
  have hs : Filter.Tendsto (fun n => inclusion D w (a n)) Filter.atTop (𝓝 x) := by
    simpa only [ha] using ht
  have he : Filter.Tendsto (fun n => evaluation D w (inclusion D w (a n))) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, hx] using ((evaluation_continuous D w).tendsto x).comp hs
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, ‖InitialThetaBoundedWittLocalization.evaluation D w (a n)‖ ≤ 1 := by
    have hnorm := he.norm
    rw [norm_zero] at hnorm
    have h := (hnorm.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ h => h.le)
    simpa only [evaluation_inclusion] using h
  have hl := (InitialThetaWittThetaQuotientTopology.localLift_tendsto_zero D w).comp he
  have hc : Filter.Tendsto (fun n => inclusion D w (corrected D w (a n))) Filter.atTop (𝓝 x) := by
    simpa only [Function.comp_def, inclusion_corrected, sub_zero] using hs.sub hl
  exact (principalIdeal_isClosed D w (primitive D w)).mem_of_tendsto hc
    (hsmall.mono (fun n hn => corrected_mem_span D w (a n) hn))

theorem kernel_eq_span : RingHom.ker (evaluation D w) = Ideal.span {primitive D w} := by
  apply le_antisymm
  · intro x hx
    exact mem_span_of_evaluation_eq_zero D w x hx
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact evaluation_primitive D w

theorem evaluation_eq_zero_iff_dvd (x : Carrier D w) :
    evaluation D w x = 0 ↔ primitive D w ∣ x := by
  change x ∈ RingHom.ker (evaluation D w) ↔ _
  rw [kernel_eq_span, Ideal.mem_span_singleton]

theorem existsUnique_primitive_quotient (x : Carrier D w) (hx : evaluation D w x = 0) :
    ∃! y : Carrier D w, primitive D w * y = x := by
  obtain ⟨y, hy⟩ := (evaluation_eq_zero_iff_dvd D w x).mp hx
  refine ⟨y, hy.symm, ?_⟩
  intro z hz
  apply (multiplication_isUniformEmbedding D w (primitive D w) (primitive_ne_zero D w)).injective
  exact hz.trans hy

def quotientPrimitiveEquiv : (Carrier D w ⧸ Ideal.span {primitive D w}) ≃+* Untilt D w :=
  (Ideal.quotEquivOfEq (kernel_eq_span D w).symm).trans (InitialThetaWittThetaSurjective.quotientEquiv D w)

theorem quotientPrimitiveEquiv_mk (x : Carrier D w) :
    quotientPrimitiveEquiv D w (Ideal.Quotient.mk _ x) = evaluation D w x := by
  exact InitialThetaWittThetaSurjective.quotientEquiv_mk D w x

end
end JoshiTeich.Act1Scene1.InitialThetaWittThetaPrincipalKernel
