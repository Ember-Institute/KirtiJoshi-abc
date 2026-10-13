import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
source-id: JT-SCENE1-LOCAL-HAAR-PRINCIPAL-INDEX
source: normalized local Haar measure in Joshi III `le:volume-lemma1`;
Mathlib `AddSubgroup.index_mul_measure` on the actual compact integer ring.
fidelity: computes integral scalar-ball measure as the inverse of its
finite additive index. Identifying this index with the place norm remains
a separate residue-field counting obligation.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField MeasureTheory
open scoped Valued

universe u
variable {K : Type u} [Field K] [NumberField K]

noncomputable abbrev integerRing (w : FinitePlace K) :=
  (Valued.v : Valuation (completionAt K w) (WithZero (Multiplicative ℤ))).integer

instance integerRing_compactSpace (w : FinitePlace K) : CompactSpace (integerRing w) := by
  refine ⟨?_⟩
  rw [Subtype.isCompact_iff]
  simpa only [Valued.toNormedField.setOfPred_mem_integer_eq_closedBall,
    Set.image_univ, Subtype.range_coe_subtype] using
    (isCompact_closedBall (0 : completionAt K w) 1)

theorem integerRing_measurableEmbedding (w : FinitePlace K) :
    MeasurableEmbedding ((↑) : integerRing w → completionAt K w) :=
  (Valued.isClosed_integer (completionAt K w)).isClosedEmbedding_subtypeVal.measurableEmbedding

/-- Pull the normalized Haar measure back to the actual compact integer ring. -/
noncomputable def integerHaar (w : FinitePlace K) : Measure (integerRing w) :=
  (normalizedHaar w).comap ((↑) : integerRing w → completionAt K w)

instance integerHaar_isAddLeftInvariant (w : FinitePlace K) :
    (integerHaar w).IsAddLeftInvariant :=
  Measure.IsAddLeftInvariant.comap (normalizedHaar w)
    (f := (integerRing w).subtype.toAddMonoidHom) (integerRing_measurableEmbedding w)

theorem integerHaar_univ (w : FinitePlace K) : integerHaar w Set.univ = 1 := by
  rw [integerHaar, (integerRing_measurableEmbedding w).comap_apply,
    Set.image_univ, Subtype.range_coe_subtype,
    Valued.toNormedField.setOfPred_mem_integer_eq_closedBall, normalizedHaar_unitBall]

theorem principalIdeal_eq_preimage_closedBall (w : FinitePlace K) (z : integerRing w) :
    (Ideal.span {z} : Set (integerRing w)) =
      ((↑) : integerRing w → completionAt K w) ⁻¹' Metric.closedBall 0 ‖(z : completionAt K w)‖ := by
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  exact Valued.toNormedField.norm_le_iff.symm

theorem principalIdeal_isOpen (w : FinitePlace K) (z : integerRing w) (hz : z ≠ 0) :
    IsOpen (Ideal.span {z} : Set (integerRing w)) := by
  rw [principalIdeal_eq_preimage_closedBall]
  exact (IsUltrametricDist.isOpen_closedBall _
    (norm_ne_zero_iff.mpr (Subtype.coe_ne_coe.mpr hz))).preimage continuous_subtype_val

theorem principalIdeal_isClosed (w : FinitePlace K) (z : integerRing w) :
    IsClosed (Ideal.span {z} : Set (integerRing w)) := by
  rw [principalIdeal_eq_preimage_closedBall]
  exact Metric.isClosed_closedBall.preimage continuous_subtype_val

instance principalIdeal_finiteIndex (w : FinitePlace K) (z : integerRing w) [NeZero z] :
    (Ideal.span {z}).toAddSubgroup.FiniteIndex := by
  letI := AddSubgroup.quotient_finite_of_isOpen (Ideal.span {z}).toAddSubgroup
    (principalIdeal_isOpen w z (NeZero.ne z))
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- The additive index of the actual integral principal ideal. -/
noncomputable def principalIndex (w : FinitePlace K) (z : integerRing w) : ℕ :=
  (Ideal.span {z}).toAddSubgroup.index

theorem principalIndex_pos (w : FinitePlace K) (z : integerRing w) (hz : z ≠ 0) :
    0 < principalIndex w z := by
  letI : NeZero z := ⟨hz⟩
  exact Nat.pos_of_ne_zero AddSubgroup.FiniteIndex.index_ne_zero

theorem principalIdeal_image (w : FinitePlace K) (z : integerRing w) :
    ((↑) : integerRing w → completionAt K w) '' (Ideal.span {z} : Set (integerRing w)) =
      (fun x : completionAt K w => (z : completionAt K w) * x) '' Metric.closedBall 0 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨a, ?_, congrArg (fun t : integerRing w => (t : completionAt K w)) ha.symm⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Valued.toNormedField.norm_le_one_iff.mpr a.property
  · rintro ⟨a, ha, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at ha
    let b : integerRing w := ⟨a, Valued.toNormedField.norm_le_one_iff.mp ha⟩
    exact ⟨z * b, Ideal.mem_span_singleton.mpr ⟨b, rfl⟩, rfl⟩

/-- Finite coset counting determines the scalar integral-ball measure. -/
theorem normalizedHaar_scalarBall_eq_inv_index
    (w : FinitePlace K) (z : integerRing w) (hz : z ≠ 0) :
    normalizedHaar w
      ((fun x : completionAt K w => (z : completionAt K w) * x) '' Metric.closedBall 0 1) =
      (principalIndex w z : ENNReal)⁻¹ := by
  letI : NeZero z := ⟨hz⟩
  have h := AddSubgroup.index_mul_measure (Ideal.span {z}).toAddSubgroup
    (principalIdeal_isClosed w z).measurableSet (integerHaar w)
  rw [integerHaar_univ] at h
  change (principalIndex w z : ENNReal) * integerHaar w (Ideal.span {z}) = 1 at h
  rw [integerHaar, (integerRing_measurableEmbedding w).comap_apply, principalIdeal_image] at h
  have h0 : (principalIndex w z : ENNReal) ≠ 0 := by
    exact_mod_cast (principalIndex_pos w z hz).ne'
  have htop : (principalIndex w z : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc
    _ = (principalIndex w z : ENNReal)⁻¹ *
        ((principalIndex w z : ENNReal) * normalizedHaar w
          ((fun x : completionAt K w => (z : completionAt K w) * x) '' Metric.closedBall 0 1)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
    _ = (principalIndex w z : ENNReal)⁻¹ := by rw [h, mul_one]

end JoshiTeich.Act1Scene1.LocalCompletion
