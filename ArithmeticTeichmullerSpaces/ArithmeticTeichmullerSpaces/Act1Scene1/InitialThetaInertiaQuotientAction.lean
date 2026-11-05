import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineInertiaQuotient
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaDivisionGroups

/-!
source-id: JT-SCENE1-ACTUAL-INERTIA-QUOTIENT-FIXED-FIELD-ACTION
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib infinite Galois correspondence.
fidelity: restricts the actual division-cover subgroup to the fixed field of
the same seed's closed normal valuation-inertia subgroup. The quotient action
is faithful, and its invariant field is the seed's original cover function field.
boundary: Scene1/Derived. This is a function-field action only; it does not
identify the quotient with an etale fundamental group or construct the geometry
producer, Cartesian cover, core, cusp, or theta-root data.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The fixed field of the seed's actual closed normal valuation-inertia subgroup. -/
def inertiaFixedField :
    IntermediateField (Genuine.baseField S.prime.EK) (Genuine.Ω S.prime.EK) :=
  IntermediateField.fixedField (Genuine.valuationInertiaSubgroup S.prime.EK)

private theorem inertiaFixedField_map_eq (pm : Bool)
    (g : S.functionFieldCoverGroup pm) :
    (S.inertiaFixedField.map g.val.toAlgHom) = S.inertiaFixedField := by
  let N := Genuine.valuationInertiaSubgroup S.prime.EK
  have hmap (x : S.inertiaFixedField) : g.val x.val ∈ S.inertiaFixedField := by
    change g.val x.val ∈ IntermediateField.fixedField N
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hconj : g.val.symm * σ * g.val ∈ N :=
      (Genuine.valuationInertiaSubgroup_normal S.prime.EK).conj_mem' σ hσ g.val
    have hx : (g.val.symm * σ * g.val) x.val = x.val := by
      have hxN : x.val ∈ IntermediateField.fixedField N := x.property
      rw [IntermediateField.mem_fixedField_iff] at hxN
      exact hxN _ hconj
    calc
      σ (g.val x.val) = g.val ((g.val.symm * σ * g.val) x.val) := by simp
      _ = g.val x.val := congrArg g.val hx
  have hmap_symm (x : S.inertiaFixedField) : g.val.symm x.val ∈ S.inertiaFixedField := by
    change g.val.symm x.val ∈ IntermediateField.fixedField N
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hconj : g.val * σ * g.val.symm ∈ N :=
      (Genuine.valuationInertiaSubgroup_normal S.prime.EK).conj_mem σ hσ g.val
    have hx : (g.val * σ * g.val.symm) x.val = x.val := by
      have hxN : x.val ∈ IntermediateField.fixedField N := x.property
      rw [IntermediateField.mem_fixedField_iff] at hxN
      exact hxN _ hconj
    calc
      σ (g.val.symm x.val) = g.val.symm ((g.val * σ * g.val.symm) x.val) := by simp
      _ = g.val.symm x.val := congrArg g.val.symm hx
  ext x
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hmap ⟨y, hy⟩
  · intro hx
    refine ⟨g.val.symm x, hmap_symm ⟨x, hx⟩, ?_⟩
    exact g.val.apply_symm_apply x

private noncomputable def inertiaFixedFieldAut (pm : Bool)
    (g : S.functionFieldCoverGroup pm) :
    S.inertiaFixedField ≃ₐ[Genuine.baseField S.prime.EK] S.inertiaFixedField :=
  (S.inertiaFixedField.equivMap g.val.toAlgHom).trans
    (IntermediateField.equivOfEq (inertiaFixedField_map_eq S pm g))

private theorem inertiaFixedFieldAut_coe (pm : Bool)
    (g : S.functionFieldCoverGroup pm) (x : S.inertiaFixedField) :
    ((inertiaFixedFieldAut S pm g x : S.inertiaFixedField) : Genuine.Ω S.prime.EK) =
      g.val x.val := by
  simp [inertiaFixedFieldAut, IntermediateField.coe_equivMap_apply]

private theorem inertiaFixedFieldAut_one_apply (pm : Bool) (x : S.inertiaFixedField) :
    inertiaFixedFieldAut S pm 1 x = x := by
  apply Subtype.ext
  calc
    ((inertiaFixedFieldAut S pm (1 : S.functionFieldCoverGroup pm) x :
        S.inertiaFixedField) : Genuine.Ω S.prime.EK) =
        (1 : Genuine.Gal S.prime.EK) x.val := inertiaFixedFieldAut_coe S pm 1 x
    _ = x.val := rfl

private theorem inertiaFixedFieldAut_mul_apply (pm : Bool)
    (g h : S.functionFieldCoverGroup pm) (x : S.inertiaFixedField) :
    inertiaFixedFieldAut S pm (g * h) x =
      inertiaFixedFieldAut S pm g (inertiaFixedFieldAut S pm h x) := by
  apply Subtype.ext
  calc
    ((inertiaFixedFieldAut S pm (g * h) x : S.inertiaFixedField) : Genuine.Ω S.prime.EK) =
        (g.val * h.val) x.val := inertiaFixedFieldAut_coe S pm (g * h) x
    _ = g.val (h.val x.val) := rfl
    _ = ((inertiaFixedFieldAut S pm g (inertiaFixedFieldAut S pm h x) :
        S.inertiaFixedField) : Genuine.Ω S.prime.EK) := by
          rw [inertiaFixedFieldAut_coe, inertiaFixedFieldAut_coe]

private def inertiaFixedFieldRestriction (pm : Bool) :
    S.functionFieldCoverGroup pm →*
      (S.inertiaFixedField ≃ₐ[Genuine.baseField S.prime.EK] S.inertiaFixedField) where
  toFun := inertiaFixedFieldAut S pm
  map_one' := by
    apply AlgEquiv.ext
    intro x
    exact inertiaFixedFieldAut_one_apply S pm x
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    exact inertiaFixedFieldAut_mul_apply S pm g h x

private theorem inertiaFixedFieldRestriction_ker (pm : Bool) :
    (inertiaFixedFieldRestriction S pm).ker =
      Genuine.inertiaKernel S.prime.EK S.prime.ℓ S.prime.M pm := by
  let N := Genuine.valuationInertiaSubgroup S.prime.EK
  ext g
  change inertiaFixedFieldAut S pm g = 1 ↔ g.val ∈ N
  constructor
  · intro hg
    have hfix : ∀ x : S.inertiaFixedField, g.val x.val = x.val := by
      intro x
      have h := congrArg (fun f : S.inertiaFixedField ≃ₐ[
          Genuine.baseField S.prime.EK] S.inertiaFixedField =>
          ((f x : S.inertiaFixedField) : Genuine.Ω S.prime.EK)) hg
      simpa only [inertiaFixedFieldAut_coe, AlgEquiv.one_apply] using h
    have hfg : g.val ∈ S.inertiaFixedField.fixingSubgroup := by
      apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      intro x hx
      exact hfix ⟨x, hx⟩
    have hN : S.inertiaFixedField.fixingSubgroup = N :=
      InfiniteGalois.fixingSubgroup_fixedField
        ⟨N, Genuine.isClosed_valuationInertiaSubgroup S.prime.EK⟩
    rw [hN] at hfg
    exact hfg
  · intro hg
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [inertiaFixedFieldAut_coe]
    have hxN : x.val ∈ IntermediateField.fixedField N := x.property
    rw [IntermediateField.mem_fixedField_iff] at hxN
    exact hxN g.val hg

/-- The actual cover quotient acts on the fixed field of actual valuation inertia. -/
def inertiaQuotientAction (pm : Bool) :
    Genuine.inertiaQuotient S.prime.EK S.prime.ℓ S.prime.M pm →*
      (S.inertiaFixedField ≃ₐ[Genuine.baseField S.prime.EK] S.inertiaFixedField) :=
  QuotientGroup.lift (Genuine.inertiaKernel S.prime.EK S.prime.ℓ S.prime.M pm)
    (inertiaFixedFieldRestriction S pm)
    (inertiaFixedFieldRestriction_ker S pm).ge

private theorem inertiaQuotientAction_mk_apply_coe (pm : Bool)
    (g : S.functionFieldCoverGroup pm) (x : S.inertiaFixedField) :
    ((inertiaQuotientAction S pm (QuotientGroup.mk g) x : S.inertiaFixedField) :
      Genuine.Ω S.prime.EK) = g.val x.val := by
  change ((inertiaFixedFieldAut S pm g x : S.inertiaFixedField) :
    Genuine.Ω S.prime.EK) = g.val x.val
  exact inertiaFixedFieldAut_coe S pm g x

/-- The actual quotient acts faithfully on the fixed field of valuation inertia. -/
theorem inertiaQuotientAction_injective (pm : Bool) :
    Function.Injective (inertiaQuotientAction S pm) := by
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr
    (inertiaFixedFieldRestriction_ker S pm).symm

set_option maxHeartbeats 1000000 in
/-- The quotient invariants in its inertia-fixed field are exactly the seed's cover field. -/
theorem inertiaQuotientAction_fixed_iff (pm : Bool) (x : S.inertiaFixedField) :
    (∀ q : Genuine.inertiaQuotient S.prime.EK S.prime.ℓ S.prime.M pm,
      inertiaQuotientAction S pm q x = x) ↔
        x.val ∈ S.functionFieldCoverField pm := by
  change (∀ q : Genuine.inertiaQuotient S.prime.EK S.prime.ℓ S.prime.M pm,
      inertiaQuotientAction S pm q x = x) ↔
    x.val ∈ Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.M pm
  constructor
  · intro h
    rw [Genuine.stabilizerField, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    let g : S.functionFieldCoverGroup pm := ⟨σ, hσ⟩
    have hg := h (QuotientGroup.mk g)
    have hval := congrArg Subtype.val hg
    simpa only [inertiaQuotientAction_mk_apply_coe] using hval
  · intro hx q
    refine QuotientGroup.induction_on q ?_
    intro g
    apply Subtype.ext
    have hx' : ∀ σ, σ ∈ Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.M pm →
        σ x.val = x.val := by
      rw [Genuine.stabilizerField, IntermediateField.mem_fixedField_iff] at hx
      exact hx
    exact hx' g.val g.property

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
