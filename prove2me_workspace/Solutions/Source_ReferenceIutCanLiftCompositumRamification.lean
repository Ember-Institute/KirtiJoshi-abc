/-
Source: lana-agents/pi1 at ca7def953193f861a462aa0831eec8f0a31ff69f (Apache-2.0),
Pi1/Orbicurve/Pullback.lean, index_inf_dvd_of_isCyclic, dvd_of_card_inf,
fixSub_sup, and ramificationIdx_sup_dvd.
-/
import Solutions.Source_ReferenceIutCanLiftGaloisRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationSquare
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open IntermediateField
open scoped Pointwise

universe u

private theorem index_inf_dvd_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H₁ H₂ : Subgroup C} {m : ℕ} (h₁ : H₁.index ∣ m) (h₂ : H₂.index ∣ m) :
    (H₁ ⊓ H₂).index ∣ m := by
  letI : CommGroup C := IsCyclic.commGroup
  have hmem (g : C) : g ^ m ∈ H₁ ⊓ H₂ := by
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    haveI : H₁.Normal := Subgroup.normal_of_isMulCommutative H₁
    haveI : H₂.Normal := Subgroup.normal_of_isMulCommutative H₂
    refine ⟨?_, ?_⟩
    · rw [ha, pow_mul]
      exact H₁.pow_mem (H₁.pow_index_mem g) a
    · rw [hb, pow_mul]
      exact H₂.pow_mem (H₂.pow_index_mem g) b
  haveI : (H₁ ⊓ H₂).Normal := Subgroup.normal_of_isMulCommutative _
  haveI : IsCyclic (C ⧸ (H₁ ⊓ H₂)) :=
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rw [Subgroup.index, ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  rintro ⟨g⟩
  change ((g ^ m : C) : C ⧸ (H₁ ⊓ H₂)) = 1
  rw [QuotientGroup.eq_one_iff]
  exact hmem g

private theorem dvd_of_card_inf {G : Type*} [Group G] [Finite G]
    {C H₁ H₂ : Subgroup G} [IsCyclic C] (h₁ : H₁ ≤ C) (h₂ : H₂ ≤ C) {d₁ d₂ e m : ℕ}
    (hd₁ : d₁ * Nat.card H₁ = Nat.card C) (hd₂ : d₂ * Nat.card H₂ = Nat.card C)
    (he : e * Nat.card (H₁ ⊓ H₂ : Subgroup G) = Nat.card C) (hm₁ : d₁ ∣ m) (hm₂ : d₂ ∣ m) :
    e ∣ m := by
  have index_eq {H : Subgroup G} {d : ℕ} (hH : H ≤ C) (hd : d * Nat.card H = Nat.card C) :
      (H.subgroupOf C).index = d := by
    have hcard := (H.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, ← hd, mul_comm d] at hcard
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard
  have hIndex₁ := index_eq h₁ hd₁
  have hIndex₂ := index_eq h₂ hd₂
  have hIndex := index_eq (inf_le_left.trans h₁) he
  have hinf : (H₁ ⊓ H₂).subgroupOf C = H₁.subgroupOf C ⊓ H₂.subgroupOf C := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hinf] at hIndex
  rw [← hIndex]
  exact index_inf_dvd_of_isCyclic (hIndex₁ ▸ hm₁) (hIndex₂ ▸ hm₂)

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
variable {N : IntermediateField (rationalBase k t) Ω}

private theorem fixSub_sup {L₁ L₂ : IntermediateField (rationalBase k t) Ω}
    (hN₁ : L₁ ≤ N) (hN₂ : L₂ ≤ N) :
    fixSub N (L₁ ⊔ L₂) = fixSub N L₁ ⊓ fixSub N L₂ := by
  have hRestrict : IntermediateField.restrict (sup_le hN₁ hN₂) =
      IntermediateField.restrict hN₁ ⊔ IntermediateField.restrict hN₂ := by
    apply IntermediateField.map_injective N.val
    rw [IntermediateField.map_sup]
    change IntermediateField.lift (IntermediateField.restrict (sup_le hN₁ hN₂)) =
      IntermediateField.lift (IntermediateField.restrict hN₁) ⊔
        IntermediateField.lift (IntermediateField.restrict hN₂)
    simp only [IntermediateField.lift_restrict]
  rw [fixSub_eq_fixingSubgroup (sup_le hN₁ hN₂), hRestrict,
    IntermediateField.fixingSubgroup_sup, ← fixSub_eq_fixingSubgroup hN₁,
    ← fixSub_eq_fixingSubgroup hN₂]

variable [CharZero k] [FiniteDimensional (rationalBase k t) N]
  [IsGalois (rationalBase k t) N]

attribute [local instance] fieldRingAction

/-- If the two relative ramification indices divide a common integer, so does the
relative ramification index of their compositum at the contracted prime. -/
theorem ramificationIdx_sup_dvd (ht : Transcendental k t)
    {F L₁ L₂ : IntermediateField (rationalBase k t) Ω}
    (h₁ : F ≤ L₁) (h₂ : F ≤ L₂) (hN₁ : L₁ ≤ N) (hN₂ : L₂ ≤ N)
    (P : Ideal (coordRing t N)) [P.IsMaximal] (_hP0 : P ≠ ⊥) {m : ℕ}
    (hm₁ : ramificationIndex h₁ (P.comap (ringMap hN₁)) ∣ m)
    (hm₂ : ramificationIndex h₂ (P.comap (ringMap hN₂)) ∣ m) :
    ramificationIndex (h₁.trans (le_sup_left : L₁ ≤ L₁ ⊔ L₂))
      (P.comap (ringMap (sup_le hN₁ hN₂))) ∣ m := by
  haveI := isCyclic_normalization_inertia ht P
  let I := P.inertia (N ≃ₐ[rationalBase k t] N)
  haveI : IsCyclic (I ⊓ fixSub N F : Subgroup _) :=
    isCyclic_of_injective (Subgroup.inclusion (inf_le_left : I ⊓ fixSub N F ≤ I))
      (Subgroup.inclusion_injective _)
  have hCard₁ := ramificationIdx_mul_card_inertia ht h₁ hN₁ P
  have hCard₂ := ramificationIdx_mul_card_inertia ht h₂ hN₂ P
  have hCard := ramificationIdx_mul_card_inertia ht
    (h₁.trans (le_sup_left : L₁ ≤ L₁ ⊔ L₂)) (sup_le hN₁ hN₂) P
  rw [fixSub_sup hN₁ hN₂, inf_inf_distrib_left] at hCard
  exact dvd_of_card_inf (inf_le_inf_left _ (fixSub_antitone h₁))
    (inf_le_inf_left _ (fixSub_antitone h₂)) hCard₁ hCard₂ hCard hm₁ hm₂

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
