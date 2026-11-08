import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineTorsionTranslationDisplacement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual generic division point and its proved rational torsion translations.
fidelity: the displacement of the existing Hgp subgroup, reduced modulo M,
is surjective and has exactly the smaller existing Hgp subgroup as kernel.
The quotient is the actual torsion quotient TK/M and its order is the
relative index of those same ambient subgroups. No field-degree or infinity
fiber statement is assumed or asserted here.
boundary: Scene1/Derived. Original group proofs. Orbicurve realization,
infinity-fiber identification and the geometry producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]
variable (n : ℕ) (hn : 0 < n)
  (TK : AddSubgroup E.toAffine.Point)
  (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
  (M : AddSubgroup E.toAffine.Point)

include hn hTK

/-- The actual displacement, reduced in the actual quotient TK/M. -/
def torsionTranslationClass :
    Hgp E n TK false →* Multiplicative (↥TK ⧸ M.addSubgroupOf TK) :=
  (QuotientAddGroup.mk' (M.addSubgroupOf TK)).toMultiplicative.comp
    (torsionTranslationDisplacement E n hn TK hTK)

/-- Every actual rank-one class is realized by an ambient translation. -/
theorem torsionTranslationClass_surjective :
    Function.Surjective (torsionTranslationClass E n hn TK hTK M) := by
  intro q
  obtain ⟨T, hT⟩ := QuotientAddGroup.mk'_surjective (M.addSubgroupOf TK) q.toAdd
  obtain ⟨σ, hσ⟩ := torsionTranslationDisplacement_surjective E n hn TK hTK
    (Multiplicative.ofAdd T)
  refine ⟨σ, ?_⟩
  change Multiplicative.ofAdd
    (QuotientAddGroup.mk' (M.addSubgroupOf TK)
      (torsionTranslationDisplacement E n hn TK hTK σ).toAdd) = q
  rw [hσ]
  exact congrArg Multiplicative.ofAdd hT

private theorem base_mem_Mbar_iff (hM : M ≤ TK) (T : ↥TK) :
    base E T.val ∈ Mbar E n M ↔ T.val ∈ M := by
  have heff : effLevel n = n := ite_eq_right (Nat.ne_of_gt hn)
  constructor
  · rintro ⟨R, hR, heq⟩
    have hRT : R = T.val := (pointMap_injective E (algebraMap k (Ω E))) heq
    exact hRT ▸ hR.1
  · intro hT
    refine ⟨T.val, ⟨hT, ?_⟩, rfl⟩
    rw [heff]
    exact hTK T.property

/-- The smaller original Hgp subgroup is exactly the kernel of displacement modulo M. -/
theorem torsionTranslationClass_ker (hM : M ≤ TK) :
    (torsionTranslationClass E n hn TK hTK M).ker =
      (Hgp E n M false).subgroupOf (Hgp E n TK false) := by
  ext σ
  change torsionTranslationClass E n hn TK hTK M σ = 1 ↔
    σ.val ∈ Hgp E n M false
  rw [mem_Hgp_false]
  let T : ↥TK := (torsionTranslationDisplacement E n hn TK hTK σ).toAdd
  have hdisp : base E T.val = act E σ.val (Qpt E n) - Qpt E n :=
    torsionTranslationDisplacement_spec E n hn TK hTK σ
  change (QuotientAddGroup.mk' (M.addSubgroupOf TK) T = 0) ↔ _
  change ((T : (↥TK ⧸ M.addSubgroupOf TK)) = 0) ↔ _
  rw [QuotientAddGroup.eq_zero_iff, ← hdisp]
  exact (base_mem_Mbar_iff E n hn TK hTK M hM T).symm

/-- The quotient by M is a genuine group quotient inside the full translation subgroup. -/
theorem torsionTranslationKernel_normal (hM : M ≤ TK) :
    ((Hgp E n M false).subgroupOf (Hgp E n TK false)).Normal := by
  rw [← torsionTranslationClass_ker E n hn TK hTK M hM]
  infer_instance

/-- The same existing Hgp subgroups have precisely the quotient TK/M. -/
def torsionTranslationQuotientEquiv (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    Hgp E n TK false ⧸ (Hgp E n M false).subgroupOf (Hgp E n TK false) ≃*
      Multiplicative (↥TK ⧸ M.addSubgroupOf TK) := by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  exact (QuotientGroup.quotientMulEquivOfEq
    (torsionTranslationClass_ker E n hn TK hTK M hM).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (torsionTranslationClass E n hn TK hTK M)
        (torsionTranslationClass_surjective E n hn TK hTK M))

/-- Consume the group identification as the relative index of the original Hgp subgroups. -/
theorem Hgp_relIndex_eq_card_torsionQuotient (hM : M ≤ TK) :
    (Hgp E n M false).relIndex (Hgp E n TK false) =
      Nat.card (↥TK ⧸ M.addSubgroupOf TK) := by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  change Nat.card (Hgp E n TK false ⧸
    (Hgp E n M false).subgroupOf (Hgp E n TK false)) = _
  exact (Nat.card_congr (torsionTranslationQuotientEquiv E n hn TK hTK M hM).toEquiv).trans
    (Nat.card_congr Multiplicative.toAdd)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
