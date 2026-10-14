import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIntegralHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRegionVolumeBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-COLLATED-INTEGRAL-HULL
source: Joshi III pr:convexes-and-hulls (3597--3609), le:volume-lemma3
(3576--3583), and the contained-region argument (3624--3631).
fidelity: constructs actual integral hulls of collated tensor subsets and
their actual Haar volume. Generator coverage derives the repeated-log-lattice
containment; component containment in the unit lattice derives compactness
and the sign bound. Collation subsets and generator coverage remain explicit
inputs. No actual theta/Bloch-Kato or different-untilt source is constructed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (ρ : iutInitialThetaVBadModuliFinset D →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (n : ℕ)
local instance collatedSourcePrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar (ρ v).1).Prime :=
  ⟨Arithmetic.residueChar_prime (ρ v).1⟩
local instance collatedIntegralModule (v : iutInitialThetaVBadModuliFinset D) :
    Module ℤ_[Arithmetic.residueChar (ρ v).1] (RepeatedThetaRoot.packet D (ρ v) n).Tensor :=
  Module.compHom (RepeatedThetaRoot.packet D (ρ v) n).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar (ρ v).1] ℚ_[Arithmetic.residueChar (ρ v).1])
variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D,
  κ → Set (RepeatedThetaRoot.packet D (ρ v) n).Tensor)

def iutInitialThetaVBadCollatedIntegralHull (v : iutInitialThetaVBadModuliFinset D) :
    Submodule ℤ_[Arithmetic.residueChar (ρ v).1] (RepeatedThetaRoot.packet D (ρ v) n).Tensor :=
  (RepeatedThetaRoot.packet D (ρ v) n).integralHull (⋃ k, C v k)

def iutInitialThetaVBadCollatedHullVolume : ℝ :=
  iutInitialThetaVBadRegionVolume D ρ n (fun v => iutInitialThetaVBadCollatedIntegralHull D ρ n C v)

theorem iutInitialThetaVBadCollatedIntegralHull_eq_iSup
    (v : iutInitialThetaVBadModuliFinset D) :
    iutInitialThetaVBadCollatedIntegralHull D ρ n C v =
      ⨆ k, (RepeatedThetaRoot.packet D (ρ v) n).integralHull (C v k) :=
  (RepeatedThetaRoot.packet D (ρ v) n).integralHull_iUnion _

theorem iutInitialThetaVBadCollatedIntegralHull_le_unitLattice
    (hunit : ∀ v k, C v k ⊆ (RepeatedThetaRoot.packet D (ρ v) n).unitLattice)
    (v : iutInitialThetaVBadModuliFinset D) :
    iutInitialThetaVBadCollatedIntegralHull D ρ n C v ≤
      (RepeatedThetaRoot.packet D (ρ v) n).unitLattice := by
  exact (RepeatedThetaRoot.packet D (ρ v) n).integralHull_le_unitLattice _
    (Set.iUnion_subset fun k => hunit v k)

variable (hgen : ∀ v, (RepeatedThetaRoot.packet D (ρ v) n).scalarGenerators
  (fun _ => iutInitialThetaFullQRootLogValue D (ρ v)) ⊆ ⋃ k, C v k)

include hgen in
theorem iutInitialThetaRepeatedRegion_le_collatedIntegralHull
    (v : iutInitialThetaVBadModuliFinset D) :
    RepeatedThetaRoot.region D (ρ v) n ≤ iutInitialThetaVBadCollatedIntegralHull D ρ n C v :=
  (RepeatedThetaRoot.packet D (ρ v) n).scalarLattice_le_integralHull _ _ (hgen v)

include hgen in
theorem iutInitialThetaVBadCollatedIntegralHull_isCompact
    (hunit : ∀ v k, C v k ⊆ (RepeatedThetaRoot.packet D (ρ v) n).unitLattice)
    (v : iutInitialThetaVBadModuliFinset D) :
    IsCompact (iutInitialThetaVBadCollatedIntegralHull D ρ n C v :
      Set (RepeatedThetaRoot.packet D (ρ v) n).Tensor) := by
  apply (RepeatedThetaRoot.packet D (ρ v) n).integralHull_isCompact _
    (fun _ => iutInitialThetaFullQRootLogValue D (ρ v)) _ (hgen v)
    (Set.iUnion_subset fun k => hunit v k)
  intro i
  change iutInitialThetaFullQRootLogValue D (ρ v) ≠ 0
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero (ρ v))

include hgen in
theorem iutInitialThetaVBadRepeatedHaarProduct_le_collatedHullVolume
    (hunit : ∀ v k, C v k ⊆ (RepeatedThetaRoot.packet D (ρ v) n).unitLattice) :
    iutInitialThetaVBadRepeatedHaarProduct D ρ n ≤
      iutInitialThetaVBadCollatedHullVolume D ρ n C := by
  apply iutInitialThetaVBadRepeatedHaarProduct_le_regionVolume D ρ n
    (fun v => iutInitialThetaVBadCollatedIntegralHull D ρ n C v)
    (fun v => iutInitialThetaRepeatedRegion_le_collatedIntegralHull D ρ n C hgen v)
  intro v
  exact (iutInitialThetaVBadCollatedIntegralHull_isCompact D ρ n C hgen hunit v).measure_lt_top.ne

variable (hρ : ∀ v, Ideal.LiesOver (ρ v).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)

include hgen hρ in
theorem iutInitialThetaVBadCollatedHullVolume_negAverageAbsLog_ge_referenceLhs
    (hn : 0 < n)
    (hunit : ∀ v k, C v k ⊆ (RepeatedThetaRoot.packet D (ρ v) n).unitLattice) :
    -(1 / (n : ℝ)) * |Real.log (iutInitialThetaVBadCollatedHullVolume D ρ n C)| ≥
      -JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  exact iutInitialThetaVBadRegionVolume_negAverageAbsLog_ge_referenceLhs D ρ n
    (fun v => iutInitialThetaVBadCollatedIntegralHull D ρ n C v) hρ hn
    (fun v => iutInitialThetaRepeatedRegion_le_collatedIntegralHull D ρ n C hgen v)
    (fun v => iutInitialThetaVBadCollatedIntegralHull_le_unitLattice D ρ n C hunit v)

end
end JoshiTeich.Act1Scene1
