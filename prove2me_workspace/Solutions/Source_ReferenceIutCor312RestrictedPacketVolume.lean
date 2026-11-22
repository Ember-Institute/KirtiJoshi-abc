import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_LogVolume
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LogVolumeData

open scoped BigOperators Classical

universe u₁ u₂ v

variable {ι : Type u₁} {V : Type u₂}
variable {C : LargeVolumeContainerData.{u₁, u₂, v} ι V}
variable (vol : LogVolumeData C) (i : Fin C.proc.length) (q : RationalPlace)

/-!
Joshi III §9.10.5 compares the weighted volume of a hull with that of
a selected tensor region. Here the product law for the supplied container
gives the exact log-volume contribution of the omitted summands.
-/

/-- A packet log-volume lower bound is equivalent to a lower bound on the
sum over the complementary components, after subtracting the selected sum. -/
theorem le_packetVol_product_iff_complement
    (U : ∀ c : C.Components i q, Set ((C.packet i q).Summand c))
    (hU : ∀ c, (U c).Nonempty)
    (S : Finset (C.Components i q)) (bound : ℝ) :
    let term (c : C.Components i q) :=
      (∏ j, vol.weight q (c j)) * vol.componentVol i q c (U c)
    bound ≤ vol.packetVol i q ((C.packet i q).productRegion U) ↔
      bound - (∑ c ∈ S, term c) ≤ ∑ c ∈ Sᶜ, term c := by
  intro term
  rw [vol.packetVol_product i q U hU]
  change bound ≤ (∑ c, term c) ↔ _
  rw [← Finset.sum_add_sum_compl S term]
  exact sub_le_iff_le_add'.symm

/-- For a selection made independently at each label, a common lower bound
on the omitted component log-volumes contributes the bound times their
total inherited product weight. -/
theorem selected_sum_add_complement_bound_le_packetVol_product
    (U : ∀ c : C.Components i q, Set ((C.packet i q).Summand c))
    (hU : ∀ c, (U c).Nonempty)
    (S : Finset (C.Fiber q)) (bound : ℝ)
    (hbound : ∀ c : C.Components i q, (¬ ∀ j, c j ∈ S) →
      bound ≤ vol.componentVol i q c (U c)) :
    let selected : Finset (C.Components i q) :=
      Fintype.piFinset fun _ : (C.proc.capsule i).LabelType => S
    let mass := ∑ w ∈ S, vol.weight q w
    let n := Fintype.card (C.proc.capsule i).LabelType
    (∑ c ∈ selected, (∏ j, vol.weight q (c j)) * vol.componentVol i q c (U c)) +
        (1 - mass ^ n) * bound ≤
      vol.packetVol i q ((C.packet i q).productRegion U) := by
  intro selected mass n
  let weight (c : C.Components i q) := ∏ j, vol.weight q (c j)
  let term (c : C.Components i q) := weight c * vol.componentVol i q c (U c)
  have hselected : (∑ c ∈ selected, weight c) = mass ^ n := by
    dsimp only [selected, mass, n, weight]
    rw [Finset.sum_prod_piFinset]
    simp
  have huniv : Fintype.piFinset
      (fun _ : (C.proc.capsule i).LabelType => (Finset.univ : Finset (C.Fiber q))) =
        (Finset.univ : Finset (C.Components i q)) := by
    ext c
    simp [Fintype.mem_piFinset]
  have hfull : (∑ c, weight c) = 1 := by
    rw [← huniv]
    dsimp only [weight]
    rw [Finset.sum_prod_piFinset]
    simp [vol.weight_sum_one q]
  have hcompl : (∑ c ∈ selectedᶜ, weight c) = 1 - mass ^ n := by
    rw [← hselected, ← hfull, ← Finset.sum_add_sum_compl selected weight, add_sub_cancel_left]
  have hle : (∑ c ∈ selectedᶜ, weight c * bound) ≤ ∑ c ∈ selectedᶜ, term c := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hc' : ¬ ∀ j, c j ∈ S := fun hs =>
      (Finset.mem_compl.mp hc) (Fintype.mem_piFinset.mpr hs)
    exact mul_le_mul_of_nonneg_left (hbound c hc')
      (Finset.prod_nonneg fun j _ => (vol.weight_pos q (c j)).le)
  rw [← Finset.sum_mul, hcompl] at hle
  change (∑ c ∈ selected, term c) + (1 - mass ^ n) * bound ≤ _
  apply (vol.le_packetVol_product_iff_complement i q U hU selected _).mpr
  change ((∑ c ∈ selected, term c) + (1 - mass ^ n) * bound) -
    (∑ c ∈ selected, term c) ≤ ∑ c ∈ selectedᶜ, term c
  rwa [add_sub_cancel_left]

end AbcAdaptation.Reference.Iut.LogVolumeData
