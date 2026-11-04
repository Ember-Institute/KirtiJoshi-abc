import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRationalRadiusTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrechetComparison

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FRECHET-TOPOLOGY
source: Joshi II `se:ff-rings`, the family of rho norms and its Frechet
completion used in `pr:teichmuller-lift-A/B`.
fidelity: proves metrizability of the original independent standard
all-radius source and its Hausdorff completion, using the rational-radius
embedding of the original closure carrier. Rational-radius coordinates
detect convergence in both original topologies. Only p and its primality
instance enter the construction; no actual place or comparison is used.
Original proofs using the project's all-radius completion comparison;
no reference implementation copied.
boundary: Scene1/Derived; preserves the original uniform structures.
Multiplicative norm equality, scalar/Frobenius/Tate-log structures and
paper B/holomorphoid/BK identities remain separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittFrechetTopology

open PadicWittFrechetSource PadicWittFrechetComparison
open scoped Topology
noncomputable section
variable (p : ℕ) [Fact p.Prime]

instance sourceMetrizable : TopologicalSpace.MetrizableSpace (Source p) :=
  (toCarrier_isUniformInducing p).isInducing.isEmbedding.metrizableSpace

instance completedMetrizable : TopologicalSpace.MetrizableSpace (Completed p) :=
  (uniformEquiv p).toHomeomorph.isEmbedding.metrizableSpace

theorem source_tendsto_iff_rational_radii {ι : Type*} (l : Filter ι)
    (f : ι → Source p) (x : Source p) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ q : PadicWittRationalRadiusTopology.RationalRadius,
      Filter.Tendsto
        (fun i => PadicWittRhoCompletion.inclusion p
          (PadicWittRationalRadiusTopology.toRadius q) ((sourceEquiv p).symm (f i))) l
        (𝓝 (PadicWittRhoCompletion.inclusion p
          (PadicWittRationalRadiusTopology.toRadius q) ((sourceEquiv p).symm x))) := by
  rw [(toCarrier_isUniformInducing p).isInducing.tendsto_nhds_iff,
    PadicWittRationalRadiusTopology.tendsto_iff_rational_coordinates]
  rfl

theorem tendsto_iff_rationalRadiusMaps {ι : Type*} (l : Filter ι)
    (f : ι → Completed p) (x : Completed p) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ q : PadicWittRationalRadiusTopology.RationalRadius,
      Filter.Tendsto
        (fun i => radiusMap p (PadicWittRationalRadiusTopology.toRadius q) (f i)) l
        (𝓝 (radiusMap p (PadicWittRationalRadiusTopology.toRadius q) x)) := by
  rw [(uniformEquiv p).toHomeomorph.isInducing.tendsto_nhds_iff,
    PadicWittRationalRadiusTopology.tendsto_iff_rational_coordinates]
  rfl

end
end JoshiTeich.Act1Scene1.PadicWittFrechetTopology
