import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedTensorRelativeWeights
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWeightDescent

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-WEIGHT-DESCENT
source: actual relative completion weights and the tensor prime-scalar descent audit.
fidelity: computes the exact obstruction on the actual selected prime fibre.
Two prime presentations give the same weighted value iff their moduli local
degrees agree. Unequal degrees exclude any region function with the raw-norm
factor formula on these presentations. No actual unequal-degree D is constructed,
and paper carrier/norm/hull identifications remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.SelectedThetaTensor
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]
local instance descentIntegralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

private theorem degree_mul_relativeWeight (i : Fin (Fintype.card ↥(fiber D p))) :
    (Arithmetic.localDeg ((packet D p).place i) : ℝ) * relativeWeight D p i =
      Arithmetic.localDeg (moduliAt D p i) := by
  rw [relativeWeight_eq_localDeg_ratio]
  change (Arithmetic.localDeg (sourceAt D p i).1 : ℝ) *
    ((Arithmetic.localDeg (moduliAt D p i) : ℝ) / Arithmetic.localDeg (sourceAt D p i).1) = _
  have hd : (Arithmetic.localDeg (sourceAt D p i).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.localDeg_pos _).ne'
  field_simp [hd]

theorem relativeWeightedPrime_eq_iff_moduliDegree_eq
    (i j : Fin (Fintype.card ↥(fiber D p))) :
    (packet D p).weightedScalarVolume (relativeWeight D p) ((packet D p).primeAtScalar i) =
      (packet D p).weightedScalarVolume (relativeWeight D p) ((packet D p).primeAtScalar j) ↔
        Arithmetic.localDeg (moduliAt D p i) = Arithmetic.localDeg (moduliAt D p j) := by
  rw [LocalCompletion.Packet.weightedScalarVolume_primeAt_eq_iff,
    degree_mul_relativeWeight, degree_mul_relativeWeight, Nat.cast_inj]

theorem no_relative_region_volume_of_distinct_moduliDegree
    (i j : Fin (Fintype.card ↥(fiber D p)))
    (hdeg : Arithmetic.localDeg (moduliAt D p i) ≠ Arithmetic.localDeg (moduliAt D p j)) :
    ¬ ∃ V : Submodule ℤ_[p] (packet D p).Tensor → ℝ,
      ∀ k, V ((packet D p).scalarLattice ((packet D p).primeAtScalar k)) =
        (packet D p).weightedScalarVolume (relativeWeight D p) ((packet D p).primeAtScalar k) := by
  rintro ⟨V, hV⟩
  apply hdeg
  apply (relativeWeightedPrime_eq_iff_moduliDegree_eq D p i j).mp
  rw [← hV i, ← hV j, LocalCompletion.Packet.primeAtScalar_lattice_eq]

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
