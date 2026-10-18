import Mathlib.Analysis.Normed.Field.Dense
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances

/-!
source-id: JT-SCENE1-COMPLETED-ALGEBRAIC-CLOSURE
source: Joshi I de:geom-base-points and Arithmetic Holomorphic Structures
lem:perfectoid; Mathlib spectralNorm and IsAlgClosed.of_denseRange.
fidelity: constructs the completed algebraic closure of an actual complete
ultrametric field of characteristic zero, including its canonical isometric
embedding. No geometric coefficient field or closedness certificate is input.
The construction supplies a local field, not a tilt identification, Berkovich
point or tempered marking. Original adapters; no reference source code copied.
boundary: Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open UniformSpace
universe u
noncomputable section
variable (E : Type u) [NontriviallyNormedField E]

/-- A distinct carrier fixes the spectral norm without changing Mathlib's algebraic closure. -/
def Algebraic := AlgebraicClosure E

instance algebraicField : Field (Algebraic E) := inferInstanceAs (Field (AlgebraicClosure E))
instance algebraicAlgebra : Algebra E (Algebraic E) := inferInstanceAs (Algebra E (AlgebraicClosure E))
instance algebraicIsAlgebraic : Algebra.IsAlgebraic E (Algebraic E) :=
  inferInstanceAs (Algebra.IsAlgebraic E (AlgebraicClosure E))
instance algebraicIsAlgClosed : IsAlgClosed (Algebraic E) :=
  inferInstanceAs (IsAlgClosed (AlgebraicClosure E))

variable [CompleteSpace E] [IsUltrametricDist E]

instance algebraicNontriviallyNormedField : NontriviallyNormedField (Algebraic E) :=
  spectralNorm.nontriviallyNormedField E (Algebraic E)

instance algebraicNormedAlgebra : NormedAlgebra E (Algebraic E) :=
  spectralNorm.normedAlgebra E (Algebraic E)

instance algebraicUltrametric : IsUltrametricDist (Algebraic E) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := E) (L := Algebraic E))

abbrev Field := Completion (Algebraic E)

instance completedNontriviallyNormedField : NontriviallyNormedField (Field E) where
  toNormedField := inferInstance
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := Algebraic E)
    exact ⟨(x : Completion (Algebraic E)), by simpa using hx⟩

instance completedUltrametric : IsUltrametricDist (Field E) := by
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x y =>
    simpa only [← Completion.coe_add, Completion.norm_coe] using
      (IsUltrametricDist.norm_add_le_max x y)

/-- The original field embeds through its spectral-norm algebraic closure. -/
def embedding : E →+* Field E := algebraMap E (Field E)

theorem embedding_norm (x : E) : ‖embedding E x‖ = ‖x‖ := norm_algebraMap' (Field E) x

theorem embedding_isometry : Isometry (embedding E) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, embedding_norm]

theorem embedding_injective : Function.Injective (embedding E) := (embedding E).injective

theorem algebraic_denseRange : DenseRange (algebraMap (Algebraic E) (Field E)) := by
  change DenseRange ((↑) : Algebraic E → Completion (Algebraic E))
  exact Completion.denseRange_coe

variable [CharZero E]

instance algebraicCharZero : CharZero (Algebraic E) :=
  charZero_of_injective_ringHom (algebraMap E (Algebraic E)).injective

instance completedCharZero : CharZero (Field E) :=
  charZero_of_injective_ringHom (embedding E).injective

instance completedIsAlgClosed : IsAlgClosed (Field E) :=
  IsAlgClosed.of_denseRange (K := Algebraic E) (L := Field E) (algebraic_denseRange E)


/-- A constructed local geometric extension keeps its carrier and proven structures together. -/
structure Extension (B : Type u) [NormedField B] where
  Carrier : Type u
  normedField : NormedField Carrier
  nontrivialNorm : letI := normedField
    ∃ x : Carrier, 1 < ‖x‖
  completeSpace : letI := normedField
    CompleteSpace Carrier
  ultrametric : letI := normedField
    IsUltrametricDist Carrier
  charZero : letI := normedField
    CharZero Carrier
  isAlgClosed : letI := normedField
    IsAlgClosed Carrier
  embedding : letI := normedField
    B →+* Carrier
  embedding_isometry : letI := normedField
    Isometry embedding

/-- Constructs every field and proof in the bundle from the completed algebraic closure. -/
def ofNormedField (B : Type u) [NormedField B] [CompleteSpace B]
    [IsUltrametricDist B] [CharZero B] (h : ∃ x : B, 1 < ‖x‖) : Extension B := by
  letI : NontriviallyNormedField B := { (inferInstance : NormedField B) with non_trivial := h }
  exact
    { Carrier := Field B
      normedField := inferInstance
      nontrivialNorm := NontriviallyNormedField.non_trivial
      completeSpace := inferInstance
      ultrametric := inferInstance
      charZero := inferInstance
      isAlgClosed := inferInstance
      embedding := embedding B
      embedding_isometry := embedding_isometry B }

end
end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
