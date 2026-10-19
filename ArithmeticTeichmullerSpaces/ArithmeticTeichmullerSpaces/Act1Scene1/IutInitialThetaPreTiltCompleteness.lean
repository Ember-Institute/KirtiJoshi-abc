import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPreTiltCompleteness
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltTopology

/-!
source-id: JT-SCENE1-INITIAL-THETA-PRETILT-COMPLETENESS
source: actual InitialThetaData geometric integer ring, its PreTilt inverse
limit and the same normed tilt inclusion. Original consumer proofs.
fidelity: proves this actual PreTilt complete and its inclusion isometric,
with closed complete range in the previously constructed tilt field.
The fraction field's completeness is not inferred merely from this closed
subring. The selected holomorphoid identity remains open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPreTiltCompleteness

open JoshiTeich.Prologue Filter
open scoped NNReal Topology
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

instance sourceNormedRing : NormedRing (InitialThetaTiltField.Source D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact GeometricPreTiltCompleteness.sourceNormedRing
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1)

instance sourceCompleteSpace : CompleteSpace (InitialThetaTiltField.Source D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact GeometricPreTiltCompleteness.sourceCompleteSpace
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1)

theorem norm_eq_sourceValuation (x : InitialThetaTiltField.Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    ‖x‖ = (InitialThetaTiltField.sourceValuation D w x : ℝ) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rfl

theorem coeff_eq_iff_dist_le (x y : InitialThetaTiltField.Source D w) (n : ℕ) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    PreTilt.coeff n x = PreTilt.coeff n y ↔ dist x y ≤
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ^
        Arithmetic.residueChar w.1 ^ n := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact GeometricPreTiltCompleteness.coeff_eq_iff_dist_le
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1) x y n

theorem inclusion_norm (x : InitialThetaTiltField.Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    ‖InitialThetaTiltField.inclusion D w x‖ = ‖x‖ := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rw [InitialThetaTiltTopology.norm_eq_valuation, InitialThetaTiltField.valuation_inclusion,
    norm_eq_sourceValuation]

theorem inclusion_isometry :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    Isometry (InitialThetaTiltField.inclusion D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, ← map_sub, inclusion_norm, dist_eq_norm]

theorem inclusion_isClosedEmbedding :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    Topology.IsClosedEmbedding (InitialThetaTiltField.inclusion D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (inclusion_isometry D w).isClosedEmbedding

theorem inclusion_range_isComplete :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    IsComplete (Set.range (InitialThetaTiltField.inclusion D w)) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (inclusion_isometry D w).isUniformInducing.isComplete_range

theorem inclusion_range_isClosed :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    IsClosed (Set.range (InitialThetaTiltField.inclusion D w)) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (inclusion_isClosedEmbedding D w).isClosed_range

/-- A Cauchy sequence of actual PreTilt elements converges before inclusion into the tilt. -/
theorem cauchySeq_converges (s : ℕ → InitialThetaTiltField.Source D w) (hs : CauchySeq s) :
    ∃ x : InitialThetaTiltField.Source D w, Tendsto s atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hs

end
end JoshiTeich.Act1Scene1.InitialThetaPreTiltCompleteness
