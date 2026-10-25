import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoCompletion
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-ULTRAMETRIC
source: Joshi II `se:ff-rings`, the nonarchimedean rho norms and the
convergence of series in the completed period algebra.
fidelity: extends the proved ultrametric addition inequality from the
actual bounded localization to each radius completion by density.
Proves that a series in a fixed-radius completion is summable exactly
when its terms tend to zero on the cofinite filter.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; Tate-log convergence needs actual coefficient
estimates. No paper B or period/BK identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoUltrametric

open JoshiTeich.Prologue
open InitialThetaWittRhoCompletion
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

theorem norm_add_le_max (ρ : Radius) (x y : Completed D w ρ) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (inclusion_denseRange D w ρ).induction_on₂
    (p := fun a b : Completed D w ρ => ‖a + b‖ ≤ max ‖a‖ ‖b‖) ?_ ?_ x y
  · exact isClosed_le (continuous_fst.add continuous_snd).norm
      (continuous_fst.norm.max continuous_snd.norm)
  · intro a b
    rw [← map_add, inclusion_norm, inclusion_norm, inclusion_norm]
    exact InitialThetaWittRhoNorm.realValue_add_le_max D w ρ.val
      ρ.property.1.ne' ρ.property.2.le a b

instance completedUltrametric (ρ : Radius) : IsUltrametricDist (Completed D w ρ) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (norm_add_le_max D w ρ)

theorem summable_iff_tendsto_cofinite_zero (ρ : Radius) {ι : Type*} (f : ι → Completed D w ρ) :
    Summable f ↔ Filter.Tendsto f Filter.cofinite (𝓝 0) :=
  NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f

theorem summable_nat_iff_tendsto_zero (ρ : Radius) (f : ℕ → Completed D w ρ) :
    Summable f ↔ Filter.Tendsto f Filter.atTop (𝓝 0) := by
  rw [summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoUltrametric
