import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoUltrametric
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusFrobenius
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecificLimits.Normed

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ALL-RADIUS-SERIES
source: Joshi II `se:ff-rings`, series in the period ring with all rho
norms, and the continuous Frobenius action on those series.
fidelity: proves summability in the existing common complete ring is
equivalent to summability in every radius coordinate. The product sum
lies in the common closed subring because all finite sums do. Hence
summability is exactly coordinatewise cofinite convergence to zero.
Coordinate evaluations and the actual Frobenius preserve these sums.
Applies the criterion to geometric series whose coordinate norms are
all less than one, and proves the resulting inverse identity.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; actual Tate-log estimates, eigenspace and
paper B/period/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusSeries

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusCompletion
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

theorem hasSum_iff_coordinates {ι : Type*} (f : ι → Carrier D w) (x : Carrier D w) :
    HasSum f x ↔ ∀ ρ : Radius, HasSum (fun i => evaluate D w ρ (f i)) (evaluate D w ρ x) := by
  simp only [HasSum, tendsto_iff_coordinates D w, map_sum]

theorem summable_iff_coordinates {ι : Type*} (f : ι → Carrier D w) :
    Summable f ↔ ∀ ρ : Radius, Summable (fun i => evaluate D w ρ (f i)) := by
  constructor
  · intro h ρ
    exact ((hasSum_iff_coordinates D w f _).mp h.hasSum ρ).summable
  · intro h
    let g : ι → Product D w := fun i => (f i).val
    have hg : Summable g := Pi.summable.mpr h
    have hm : (∑' i, g i) ∈ commonSubring D w := by
      apply (Subring.isClosed_topologicalClosure (diagonal D w).range).mem_of_tendsto hg.hasSum
      exact Filter.Eventually.of_forall (fun s : Finset ι =>
        (commonSubring D w).sum_mem (fun i _ => (f i).property))
    refine ⟨⟨∑' i, g i, hm⟩, ?_⟩
    apply (hasSum_iff_coordinates D w f _).mpr
    exact Pi.hasSum.mp hg.hasSum

theorem summable_iff_coordinates_tendsto_zero {ι : Type*} (f : ι → Carrier D w) :
    Summable f ↔ ∀ ρ : Radius,
      Filter.Tendsto (fun i => evaluate D w ρ (f i)) Filter.cofinite (𝓝 0) := by
  rw [summable_iff_coordinates]
  exact forall_congr' (fun ρ => InitialThetaWittRhoUltrametric.summable_iff_tendsto_cofinite_zero
    D w ρ (fun i => evaluate D w ρ (f i)))

theorem summable_nat_iff_coordinates_tendsto_zero (f : ℕ → Carrier D w) :
    Summable f ↔ ∀ ρ : Radius,
      Filter.Tendsto (fun n => evaluate D w ρ (f n)) Filter.atTop (𝓝 0) := by
  rw [summable_iff_coordinates_tendsto_zero, Nat.cofinite_eq_atTop]

theorem summable_iff_tendsto_cofinite_zero {ι : Type*} (f : ι → Carrier D w) :
    Summable f ↔ Filter.Tendsto f Filter.cofinite (𝓝 0) := by
  rw [summable_iff_coordinates_tendsto_zero, tendsto_iff_coordinates D w]
  simp only [map_zero]

theorem summable_nat_iff_tendsto_zero (f : ℕ → Carrier D w) :
    Summable f ↔ Filter.Tendsto f Filter.atTop (𝓝 0) := by
  rw [summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]

theorem evaluate_tsum {ι : Type*} (f : ι → Carrier D w) (hf : Summable f) (ρ : Radius) :
    evaluate D w ρ (∑' i, f i) = ∑' i, evaluate D w ρ (f i) :=
  hf.map_tsum (evaluate D w ρ) (evaluate_continuous D w ρ)

theorem hasSum_frobenius {ι : Type*} (f : ι → Carrier D w) (x : Carrier D w) (hf : HasSum f x) :
    HasSum (fun i => InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (f i))
      (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x) :=
  hf.map (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).toRingHom
    (InitialThetaWittAllRadiusFrobenius.frobenius_continuous D w)

theorem frobenius_tsum {ι : Type*} (f : ι → Carrier D w) (hf : Summable f) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (∑' i, f i) =
      ∑' i, InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (f i) :=
  (hasSum_frobenius D w f _ hf.hasSum).tsum_eq.symm

theorem summable_powers (x : Carrier D w)
    (hx : ∀ ρ : Radius, coordinateSeminorm D w ρ x < 1) : Summable (fun n : ℕ => x ^ n) := by
  apply (summable_nat_iff_coordinates_tendsto_zero D w _).mpr
  intro ρ
  simpa only [map_pow] using
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hx ρ) :
      Filter.Tendsto (fun n : ℕ => evaluate D w ρ x ^ n) Filter.atTop (𝓝 0))

theorem tsum_powers_mul_one_sub (x : Carrier D w)
    (hx : ∀ ρ : Radius, coordinateSeminorm D w ρ x < 1) :
    (∑' n : ℕ, x ^ n) * (1 - x) = 1 := by
  apply InitialThetaWittAllRadiusCompletion.ext D w
  intro ρ
  rw [map_mul, evaluate_tsum D w _ (summable_powers D w x hx), map_sub, map_one]
  simpa only [map_pow] using (summable_geometric_of_norm_lt_one (hx ρ)).tsum_pow_mul_one_sub

end
end JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusSeries
