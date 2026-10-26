import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenRadiusDynamics
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRadiusInterpolation
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-RADIUS-TOPOLOGY
source: Joshi II `se:ff-rings` and the B^{phi=p} space in the period
sequence in the proof of `pr:teichmuller-lift-A`.
fidelity: uses the actual eigenvalue equation, Frobenius radius dynamics
and proved endpoint interpolation to show that any single radius detects
the original topology on the entire phi=p subspace. That subspace is
closed and complete in the original common ring. Its actual evaluation
into every fixed-radius completion is a uniform and closed embedding.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no smaller logarithmic image replaces the
eigen subspace, and no topology is changed. Full period representation
and period/BK identities remain open. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenRadiusTopology

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusCompletion InitialThetaWittAdditiveTatePeriod
open InitialThetaWittEigenRadiusDynamics
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem tendsto_coordinate_of_fixed {ι : Type*} (l : Filter ι) (f : ι → Eigen D w)
    (ρ r : Radius)
    (hρ : Filter.Tendsto (fun i => coordinateSeminorm D w ρ (f i).val) l (𝓝 0)) :
    Filter.Tendsto (fun i => coordinateSeminorm D w r (f i).val) l (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_radiusOrbit_le D w r ρ
  obtain ⟨m, hm⟩ := exists_radiusOrbit_le D w ρ (radiusOrbit D w r n)
  have ha := (tendsto_radiusOrbit_iff D w l f ρ m).mpr hρ
  have hmax := ha.max hρ
  have hmid : Filter.Tendsto
      (fun i => coordinateSeminorm D w (radiusOrbit D w r n) (f i).val) l (𝓝 0) := by
    apply squeeze_zero (fun i => apply_nonneg _ _) (fun i => ?_) (by simpa only [max_self] using hmax)
    exact InitialThetaWittRadiusInterpolation.coordinateSeminorm_le_endpoint_max D w
      (radiusOrbit D w ρ m) (radiusOrbit D w r n) ρ hm hn (f i).val
  exact (tendsto_radiusOrbit_iff D w l f r n).mp hmid

theorem tendsto_zero_iff_fixedCoordinate {ι : Type*} (l : Filter ι) (f : ι → Eigen D w)
    (ρ : Radius) : Filter.Tendsto f l (𝓝 0) ↔
      Filter.Tendsto (fun i => coordinateSeminorm D w ρ (f i).val) l (𝓝 0) := by
  constructor
  · intro h
    have ht := (coordinateSeminorm_continuous D w ρ).tendsto (0 : Carrier D w)
    rw [map_zero] at ht
    exact ht.comp (tendsto_subtype_rng.mp h)
  · intro h
    apply tendsto_subtype_rng.mpr
    apply (tendsto_iff_coordinates D w l (fun i => (f i).val) 0).mpr
    intro r
    rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_coordinate_of_fixed D w l f ρ r h

def evaluationHom (ρ : Radius) : Eigen D w →+ InitialThetaWittRhoCompletion.Completed D w ρ :=
  (evaluate D w ρ).toAddMonoidHom.comp (frobeniusPrimeSubmodule D w).subtype.toAddMonoidHom

theorem evaluationHom_continuous (ρ : Radius) : Continuous (evaluationHom D w ρ) :=
  (evaluate_continuous D w ρ).comp continuous_subtype_val

theorem evaluationHom_injective (ρ : Radius) : Function.Injective (evaluationHom D w ρ) := by
  intro x y h
  apply Subtype.ext
  exact InitialThetaWittRadiusFaithfulness.evaluate_injective D w ρ h

theorem tendsto_iff_evaluationHom {ι : Type*} (l : Filter ι) (f : ι → Eigen D w)
    (x : Eigen D w) (ρ : Radius) : Filter.Tendsto f l (𝓝 x) ↔
      Filter.Tendsto (fun i => evaluationHom D w ρ (f i)) l (𝓝 (evaluationHom D w ρ x)) := by
  constructor
  · intro h
    exact ((evaluationHom_continuous D w ρ).tendsto x).comp h
  · intro h
    have hzero := h.sub_const (evaluationHom D w ρ x)
    rw [sub_self] at hzero
    have hn : Filter.Tendsto
        (fun i => coordinateSeminorm D w ρ ((f i - x : Eigen D w) : Carrier D w)) l (𝓝 0) := by
      change Filter.Tendsto (fun i => ‖evaluationHom D w ρ (f i - x)‖) l (𝓝 0)
      simpa only [map_sub, norm_zero] using hzero.norm
    have hs := (tendsto_zero_iff_fixedCoordinate D w l (fun i => f i - x) ρ).mpr hn
    exact tendsto_sub_nhds_zero_iff.mp hs

theorem evaluationHom_isInducing (ρ : Radius) : Topology.IsInducing (evaluationHom D w ρ) := by
  apply Topology.isInducing_iff_nhds.mpr
  intro x
  apply le_antisymm
  · exact ((evaluationHom_continuous D w ρ).tendsto x).le_comap
  · have h := (tendsto_iff_evaluationHom D w
      (Filter.comap (evaluationHom D w ρ) (𝓝 (evaluationHom D w ρ x))) id x ρ).mpr
        Filter.tendsto_comap
    exact Filter.tendsto_id'.mp h

theorem evaluationHom_isEmbedding (ρ : Radius) : Topology.IsEmbedding (evaluationHom D w ρ) :=
  (evaluationHom_isInducing D w ρ).isEmbedding

theorem eigen_isClosed : IsClosed (frobeniusPrimeSubmodule D w : Set (Carrier D w)) := by
  change IsClosed {x : Carrier D w | InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x =
    (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x}
  simpa only [Nat.cast_smul_eq_nsmul, Pi.smul_apply, id_eq] using
    isClosed_eq (InitialThetaWittAllRadiusFrobenius.frobenius_continuous D w)
      (continuous_id.nsmul (Arithmetic.residueChar w.1))

instance eigenComplete : CompleteSpace (Eigen D w) := (eigen_isClosed D w).isComplete.completeSpace_coe

instance eigenIsUniformAddGroup : IsUniformAddGroup (Eigen D w) := by
  let : IsUniformAddGroup (Carrier D w) := (commonSubring D w).toAddSubgroup.isUniformAddGroup
  exact (frobeniusPrimeSubmodule D w).toAddSubgroup.isUniformAddGroup

theorem evaluationHom_isUniformEmbedding (ρ : Radius) : IsUniformEmbedding (evaluationHom D w ρ) :=
  AddMonoidHom.isUniformEmbedding_of_isEmbedding (evaluationHom_isEmbedding D w ρ)

theorem evaluationHom_isClosedEmbedding (ρ : Radius) :
    Topology.IsClosedEmbedding (evaluationHom D w ρ) :=
  (evaluationHom_isUniformEmbedding D w ρ).isClosedEmbedding

theorem evaluationHom_range_isClosed (ρ : Radius) : IsClosed (Set.range (evaluationHom D w ρ)) :=
  (evaluationHom_isClosedEmbedding D w ρ).isClosed_range

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenRadiusTopology
