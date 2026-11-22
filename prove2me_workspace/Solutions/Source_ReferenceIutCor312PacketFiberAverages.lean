import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_LogVolume
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LogVolumeData

open scoped BigOperators Classical

universe u₁ u₂ u₃ v

variable {ι : Type u₁} {V : Type u₂} {M : Type u₃}
variable {C : LargeVolumeContainerData.{u₁, u₂, v} ι V}
variable (vol : LogVolumeData C) (i : Fin C.proc.length) (q : RationalPlace)
variable (contract : C.Fiber q → M)

/-- The conditional average of component log-volumes over all lifts of a
tuple of moduli places. Its denominator is the inherited weight of the fibre. -/
noncomputable def conditionalComponentVol
    (U : ∀ c : C.Components i q, Set ((C.packet i q).Summand c))
    (b : (C.proc.capsule i).LabelType → M) : ℝ :=
  let fiber := (Finset.univ : Finset (C.Components i q)).filter (fun c => contract ∘ c = b)
  let weight (c : C.Components i q) := ∏ j, vol.weight q (c j)
  (∑ c ∈ fiber, weight c * vol.componentVol i q c (U c)) / (∑ c ∈ fiber, weight c)

variable [Fintype M]
variable (moduliWeight : M → ℝ) (hpos : ∀ w, 0 < moduliWeight w)
variable (hpush : ∀ w : M,
  (∑ x ∈ (Finset.univ : Finset (C.Fiber q)).filter (fun x => contract x = w),
    vol.weight q x) = moduliWeight w)

include hpos hpush

/-- Regroup the full direct-product packet over its moduli tuples. The
one-place weight identity gives the tensor-product weight of every fibre. -/
theorem packetVol_product_eq_sum_conditionalComponentVol
    (U : ∀ c : C.Components i q, Set ((C.packet i q).Summand c))
    (hU : ∀ c, (U c).Nonempty) :
    vol.packetVol i q ((C.packet i q).productRegion U) =
      ∑ b : (C.proc.capsule i).LabelType → M,
        (∏ j, moduliWeight (b j)) * vol.conditionalComponentVol i q contract U b := by
  let term (c : C.Components i q) :=
    (∏ j, vol.weight q (c j)) * vol.componentVol i q c (U c)
  rw [vol.packetVol_product i q U hU]
  change (∑ c, term c) = _
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (C.Components i q))
    (fun c => contract ∘ c) term]
  refine Finset.sum_congr rfl fun b _ => ?_
  let placeFiber (j : (C.proc.capsule i).LabelType) :=
    (Finset.univ : Finset (C.Fiber q)).filter (fun w => contract w = b j)
  have hfiber :
      (Finset.univ : Finset (C.Components i q)).filter (fun c => contract ∘ c = b) =
        Fintype.piFinset placeFiber := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      placeFiber, funext_iff, Function.comp_apply]
  have hmass :
      (∑ c ∈ (Finset.univ : Finset (C.Components i q)).filter (fun c => contract ∘ c = b),
        ∏ j, vol.weight q (c j)) = ∏ j, moduliWeight (b j) := by
    rw [hfiber, ← Finset.prod_univ_sum placeFiber (fun _ w => vol.weight q w)]
    exact Finset.prod_congr rfl fun j _ => hpush (b j)
  have hmass_pos : 0 < ∏ j, moduliWeight (b j) :=
    Finset.prod_pos fun j _ => hpos (b j)
  dsimp only [conditionalComponentVol]
  rw [hmass]
  exact (mul_div_cancel₀ _ hmass_pos.ne').symm

/-- Fibre lower bounds imply the corresponding weighted lower bound on the
full packet, as required by the finite-place packet comparison. -/
theorem sum_moduli_bounds_le_packetVol_product
    (U : ∀ c : C.Components i q, Set ((C.packet i q).Summand c))
    (hU : ∀ c, (U c).Nonempty)
    (lower : ((C.proc.capsule i).LabelType → M) → ℝ)
    (hlower : ∀ b, lower b ≤ vol.conditionalComponentVol i q contract U b) :
    (∑ b, (∏ j, moduliWeight (b j)) * lower b) ≤
      vol.packetVol i q ((C.packet i q).productRegion U) := by
  rw [vol.packetVol_product_eq_sum_conditionalComponentVol i q contract
    moduliWeight hpos hpush U hU]
  exact Finset.sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_left (hlower b) (Finset.prod_nonneg fun j _ => (hpos (b j)).le)

end AbcAdaptation.Reference.Iut.LogVolumeData
