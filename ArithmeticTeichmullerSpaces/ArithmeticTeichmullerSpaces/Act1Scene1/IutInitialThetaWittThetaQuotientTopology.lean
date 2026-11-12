import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaSurjective
import Mathlib.Topology.Algebra.Ring.Ideal

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-THETA-QUOTIENT-TOPOLOGY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, the
original untilt as a continuous quotient of the period carrier.
fidelity: the actual integral Teichmuller lift gives a local right
inverse at zero with bounds at every radius simultaneously. It tends
to zero for the original Frechet topology. Translated local lifts prove
the evaluation is open. The proved algebraic quotient equivalence is
then a homeomorphism for the actual quotient topology.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no continuity of the lift away from zero,
principal-kernel identity or arbitrary-untilt transport is asserted.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittThetaQuotientTopology

open JoshiTeich.Prologue InitialThetaWittThetaBound InitialThetaWittThetaEvaluation
open InitialThetaWittThetaSurjective InitialThetaWittThetaTateFiber
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def localLift (z : Untilt D w) : InitialThetaWittAllRadiusCompletion.Carrier D w :=
  if hz : ‖z‖ ≤ 1 then
    teichLift D w ⟨z, (LocalGeometricFontaine.mem_integerRing _ _).mpr hz⟩ else 0

theorem coordinateSeminorm_localLift_le (ρ : InitialThetaWittRhoCompletion.Radius) (z : Untilt D w) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (localLift D w z) ≤ ‖z‖ := by
  unfold localLift
  split_ifs with hz
  · have hn : ‖(⟨z, (LocalGeometricFontaine.mem_integerRing _ _).mpr hz⟩ :
        LocalGeometricFontaine.integerRing (Untilt D w))‖ = ‖z‖ := rfl
    exact (coordinateSeminorm_teichLift D w ρ _).le.trans_eq hn
  · rw [map_zero]
    exact norm_nonneg z

theorem evaluation_localLift (z : Untilt D w) (hz : ‖z‖ ≤ 1) :
    evaluation D w (localLift D w z) = z := by
  rw [localLift, dif_pos hz]
  exact evaluation_teichLift D w _

theorem localLift_tendsto_zero :
    Filter.Tendsto (localLift D w) (𝓝 (0 : Untilt D w))
      (𝓝 (0 : InitialThetaWittAllRadiusCompletion.Carrier D w)) := by
  apply (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w _ _ _).mpr
  intro ρ
  rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
  change Filter.Tendsto (fun z : Untilt D w =>
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (localLift D w z)) (𝓝 0) (𝓝 0)
  exact squeeze_zero
    (fun z => apply_nonneg (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ) _)
    (coordinateSeminorm_localLift_le D w ρ)
    (by simpa only [norm_zero] using continuous_norm.tendsto (0 : Untilt D w))

theorem evaluation_isOpenMap : IsOpenMap (evaluation D w) := by
  apply IsOpenMap.of_nhds_le
  intro x
  let g : Untilt D w → InitialThetaWittAllRadiusCompletion.Carrier D w :=
    fun z => x + localLift D w (z - evaluation D w x)
  have hd : Filter.Tendsto (fun z : Untilt D w => z - evaluation D w x)
      (𝓝 (evaluation D w x)) (𝓝 0) := by
    have h : Continuous (fun z : Untilt D w => z - evaluation D w x) :=
      continuous_id.sub continuous_const
    simpa only [sub_self] using h.tendsto (evaluation D w x)
  have hg : Filter.Tendsto g (𝓝 (evaluation D w x)) (𝓝 x) := by
    simpa only [g, Function.comp_def, add_zero] using ((localLift_tendsto_zero D w).comp hd).const_add x
  have hn : Filter.Tendsto (fun z : Untilt D w => ‖z - evaluation D w x‖)
      (𝓝 (evaluation D w x)) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto (0 : Untilt D w)).comp hd
  have hsmall : ∀ᶠ z in 𝓝 (evaluation D w x), ‖z - evaluation D w x‖ < 1 :=
    hn.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hfg : ∀ᶠ z in 𝓝 (evaluation D w x), evaluation D w (g z) = z := by
    filter_upwards [hsmall] with z hz
    dsimp only [g]
    rw [map_add, evaluation_localLift D w _ hz.le, add_comm, sub_add_cancel]
  calc
    𝓝 (evaluation D w x) = Filter.map id (𝓝 (evaluation D w x)) := Filter.map_id.symm
    _ = Filter.map ((evaluation D w) ∘ g) (𝓝 (evaluation D w x)) := (Filter.map_congr hfg).symm
    _ = Filter.map (evaluation D w) (Filter.map g (𝓝 (evaluation D w x))) := Filter.map_map.symm
    _ ≤ Filter.map (evaluation D w) (𝓝 x) := Filter.map_mono hg

theorem evaluation_isOpenQuotientMap : IsOpenQuotientMap (evaluation D w) :=
  ⟨evaluation_surjective D w, evaluation_continuous D w, evaluation_isOpenMap D w⟩

theorem quotientEquiv_continuous : Continuous (quotientEquiv D w) := by
  apply (QuotientRing.isOpenQuotientMap_mk (RingHom.ker (evaluation D w))).isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, quotientEquiv_mk] using evaluation_continuous D w

theorem quotientEquiv_isOpenMap : IsOpenMap (quotientEquiv D w) := by
  apply (QuotientRing.isOpenQuotientMap_mk (RingHom.ker (evaluation D w))).isOpenMap_iff.mpr
  simpa only [Function.comp_def, quotientEquiv_mk] using evaluation_isOpenMap D w

def quotientHomeomorph :
    (InitialThetaWittAllRadiusCompletion.Carrier D w ⧸ RingHom.ker (evaluation D w)) ≃ₜ Untilt D w :=
  (quotientEquiv D w).toEquiv.toHomeomorphOfContinuousOpen
    (quotientEquiv_continuous D w) (quotientEquiv_isOpenMap D w)

theorem quotientHomeomorph_mk (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    quotientHomeomorph D w (Ideal.Quotient.mk (RingHom.ker (evaluation D w)) x) = evaluation D w x :=
  quotientEquiv_mk D w x

end
end JoshiTeich.Act1Scene1.InitialThetaWittThetaQuotientTopology
