/-
original-path: `refer/iut/Iut/Anabelian/Existence.lean` (coord₂, coord₂_ker,
coord₂_surjective, QIso, q, and epsilon_graph).
original-author: Christian Merten <lana@merten.dev>
original-commit: `a36b42b9a221e1baaf434bb76c85b3a0dfbf33a7`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source's 2026 iut contributors notice and Apache-2.0
license before copying; the notice is retained below.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(f); IUT IV Corollary 2.2, proof (P7);
Joshi III `ss:theta-data-fixing2` and `ss:val-sets-defn`.
fidelity: copied the second-coordinate kernel and surjectivity proofs; adapted
the quotient to actual global/local elliptic torsion groups. Proved completion
transport and the canonical-generator criterion without model geometry.
boundary: Scene1/Derived. Geometric realization as a cusp of the required
orbicurve, its covering diagram, and its theta-root identity remain open.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaValuationSection

namespace JoshiTeich.ReferenceIut.AdmissiblePrimeData

open WeierstrassCurve NumberField JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

universe u
noncomputable section

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable (P : AdmissiblePrimeData F E Fbar VBad) [NumberField ↥P.torsionField]

attribute [local instance 1100] instDecidableEqK

local instance : Fact P.ℓ.Prime := ⟨P.ℓ_prime⟩

/-- The second coordinate `E(K)[ℓ] → 𝔽_ℓ`, with kernel `M`. -/
def coord₂ : ↥P.TK →+ ZMod P.ℓ :=
  (Pi.evalAddMonoidHom (fun _ => ZMod P.ℓ) 1).comp P.basisK.toAddMonoidHom

lemma coord₂_ker : P.coord₂.ker = P.M.addSubgroupOf P.TK := by
  ext R
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, ← P.mem_toV_iff, P.toV_M]
  unfold M₀ coord₂
  rw [AddSubgroup.mem_zmultiples_iff]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
    AddEquiv.coe_toAddMonoidHom]
  constructor
  · intro h
    refine ⟨(P.basisK R 0).cast, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp [h]
  · rintro ⟨n, hn⟩
    have := congrFun hn 1
    simpa using this.symm

lemma coord₂_surjective : Function.Surjective P.coord₂ := by
  intro a
  refine ⟨P.basisK.symm (Pi.single 1 a), ?_⟩
  simp [coord₂]


/-- The actual rank-one quotient of the global torsion by the chosen line. -/
abbrev rankOneQuotient : Type u := ↥P.TK ⧸ P.M.addSubgroupOf P.TK

/-- Projection of a global torsion point to its rank-one class. -/
abbrev rankOneClass : ↥P.TK →+ P.rankOneQuotient :=
  QuotientAddGroup.mk' (P.M.addSubgroupOf P.TK)

/-- The second coordinate identifies the actual quotient with `ZMod ℓ`. -/
def rankOneEquiv : P.rankOneQuotient ≃+ ZMod P.ℓ :=
  (QuotientAddGroup.quotientAddEquivOfEq P.coord₂_ker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective P.coord₂ P.coord₂_surjective)

@[simp] lemma rankOneEquiv_class (R : ↥P.TK) :
    P.rankOneEquiv (P.rankOneClass R) = P.coord₂ R := rfl

/-- The distinguished nonzero class in the actual global quotient. -/
def distinguishedClass : P.rankOneQuotient := P.rankOneClass P.e₂

@[simp] lemma rankOneEquiv_distinguishedClass :
    P.rankOneEquiv P.distinguishedClass = 1 := by
  rw [distinguishedClass, rankOneEquiv_class]
  simp [coord₂, e₂]

lemma distinguishedClass_ne_zero : P.distinguishedClass ≠ 0 := by
  intro h
  have := congrArg P.rankOneEquiv h
  simpa using this

/-- The two canonical classes remain distinct because the admissible prime is odd. -/
lemma distinguishedClass_ne_neg : P.distinguishedClass ≠ -P.distinguishedClass := by
  letI : Fact (2 < P.ℓ) := ⟨by have := P.five_le; omega⟩
  intro h
  apply (ZMod.neg_one_ne_one (n := P.ℓ))
  have hc := congrArg P.rankOneEquiv h
  simpa only [map_neg, rankOneEquiv_distinguishedClass] using hc.symm

lemma card_rankOneQuotient : Nat.card P.rankOneQuotient = P.ℓ := by
  rw [Nat.card_congr P.rankOneEquiv.toEquiv]
  exact Nat.card_zmod P.ℓ

lemma rankOneClass_eq_iff (R T : ↥P.TK) :
    P.rankOneClass R = P.rankOneClass T ↔
      (R : P.EK.toAffine.Point) - (T : P.EK.toAffine.Point) ∈ P.M := by
  exact QuotientAddGroup.eq_iff_sub_mem

variable (TF : TateFamily E P.torsionField P.ℓ VBad)

/-- Canonical generators at the selected place give exactly the two global classes. -/
lemma canonical_iff_rankOneClass {v : FinitePlace ↥(fieldOfModuli F E)}
    (hv : v ∈ VBad) (R : ↥P.TK) :
    TF.IsCanonicalAt (P.sectFin TF v) (P.sectFin_isBad TF hv) R ↔
      P.rankOneClass R = P.distinguishedClass ∨
        P.rankOneClass R = -P.distinguishedClass := by
  change TF.IsCanonicalAt _ _ (R : P.EK.toAffine.Point) ↔
    P.rankOneClass R = P.rankOneClass P.e₂ ∨
      P.rankOneClass R = -P.rankOneClass P.e₂
  rw [← map_neg, P.rankOneClass_eq_iff, P.rankOneClass_eq_iff]
  simpa only [AddSubgroup.coe_neg, sub_neg_eq_add] using
    P.sectFin_canonical_iff TF hv (R : P.EK.toAffine.Point)

/-- Completion on the actual torsion subgroups. -/
def localTorsionMap (w : FinitePlace ↥P.torsionField) :
    ↥P.TK →+ ↥(TateStructure.torsion P.ℓ (curveKw E P.torsionField w)) :=
  ((TateFamily.toLocal P w).domRestrict P.TK).codRestrict _
    (fun R => TateFamily.toLocal_mem_torsion P R.2)

@[simp] lemma coe_localTorsionMap (w : FinitePlace ↥P.torsionField) (R : ↥P.TK) :
    (P.localTorsionMap w R : (curveKw E P.torsionField w).toAffine.Point) =
      TateFamily.toLocal P w R := rfl

include TF in
lemma localTorsionMap_bijective {w : FinitePlace ↥P.torsionField}
    (hw : IsBadPlace E P.torsionField VBad w) : Function.Bijective (P.localTorsionMap w) := by
  constructor
  · intro R T h
    apply Subtype.ext
    apply pointMap_injective P.EK (emb P.torsionField w)
    exact congrArg Subtype.val h
  · intro Q
    obtain ⟨R, hR, hRQ⟩ := TF.exists_toLocal_eq P hw Q.2
    exact ⟨⟨R, hR⟩, Subtype.ext hRQ⟩

/-- Every local torsion point comes from the same global torsion field. -/
def localTorsionEquiv {w : FinitePlace ↥P.torsionField}
    (hw : IsBadPlace E P.torsionField VBad w) :
    ↥P.TK ≃+ ↥(TateStructure.torsion P.ℓ (curveKw E P.torsionField w)) :=
  AddEquiv.ofBijective (P.localTorsionMap w) (P.localTorsionMap_bijective TF hw)

@[simp] lemma localTorsionEquiv_apply {w : FinitePlace ↥P.torsionField}
    (hw : IsBadPlace E P.torsionField VBad w) (R : ↥P.TK) :
    P.localTorsionEquiv TF hw R = P.localTorsionMap w R := rfl

variable {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad)

/-- The actual local graph line, regarded as a subgroup of local torsion. -/
abbrev selectedGraphLine :=
  ((TF.S (P.sectFin TF v) (P.sectFin_isBad TF hv)).graphLine P.ℓ).addSubgroupOf
    (TateStructure.torsion P.ℓ (curveKw E P.torsionField (P.sectFin TF v)))

/-- Completion carries the global chosen line onto the selected local graph line. -/
lemma localTorsionEquiv_map_line :
    (P.M.addSubgroupOf P.TK).map
      (P.localTorsionEquiv TF (P.sectFin_isBad TF hv)).toAddMonoidHom =
        P.selectedGraphLine TF hv := by
  ext Q
  obtain ⟨R, rfl⟩ := (P.localTorsionEquiv TF (P.sectFin_isBad TF hv)).surjective Q
  rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply]
  simp only [localTorsionEquiv_apply]
  change (R : P.EK.toAffine.Point) ∈ P.M ↔
    (R : P.EK.toAffine.Point) ∈ TF.graphLineAt _ (P.sectFin_isBad TF hv)
  rw [P.sectFin_graphLine TF hv]

/-- The actual quotient of local elliptic torsion by its graph line. -/
abbrev selectedGraphQuotient : Type u :=
  ↥(TateStructure.torsion P.ℓ (curveKw E P.torsionField (P.sectFin TF v))) ⧸
    P.selectedGraphLine TF hv

/-- Completion induces an isomorphism of the global and local rank-one quotients. -/
def selectedGraphQuotientEquiv : P.rankOneQuotient ≃+ P.selectedGraphQuotient TF hv :=
  QuotientAddGroup.congr _ _ (P.localTorsionEquiv TF (P.sectFin_isBad TF hv))
    (P.localTorsionEquiv_map_line TF hv)

@[simp] lemma selectedGraphQuotientEquiv_class (R : ↥P.TK) :
    P.selectedGraphQuotientEquiv TF hv (P.rankOneClass R) =
      QuotientAddGroup.mk' (P.selectedGraphLine TF hv)
        (P.localTorsionMap (P.sectFin TF v) R) := rfl

/-- The distinguished local class is the completion of the global one. -/
def selectedDistinguishedClass : P.selectedGraphQuotient TF hv :=
  P.selectedGraphQuotientEquiv TF hv P.distinguishedClass

lemma selectedDistinguishedClass_ne_zero : P.selectedDistinguishedClass TF hv ≠ 0 := by
  intro h
  apply P.distinguishedClass_ne_zero
  apply (P.selectedGraphQuotientEquiv TF hv).injective
  simpa only [selectedDistinguishedClass, map_zero] using h

lemma selectedDistinguishedClass_ne_neg :
    P.selectedDistinguishedClass TF hv ≠ -P.selectedDistinguishedClass TF hv := by
  intro h
  apply P.distinguishedClass_ne_neg
  apply (P.selectedGraphQuotientEquiv TF hv).injective
  simpa only [selectedDistinguishedClass, map_neg] using h

lemma card_selectedGraphQuotient : Nat.card (P.selectedGraphQuotient TF hv) = P.ℓ := by
  rw [← Nat.card_congr (P.selectedGraphQuotientEquiv TF hv).toEquiv]
  exact P.card_rankOneQuotient

/-- Every canonical local generator is exactly one of the two distinguished classes. -/
theorem selectedCanonical_iff_class
    (Q : ↥(TateStructure.torsion P.ℓ
      (curveKw E P.torsionField (P.sectFin TF v)))) :
    (TF.S (P.sectFin TF v) (P.sectFin_isBad TF hv)).IsCanonical P.ℓ Q ↔
      QuotientAddGroup.mk' (P.selectedGraphLine TF hv) Q =
          P.selectedDistinguishedClass TF hv ∨
        QuotientAddGroup.mk' (P.selectedGraphLine TF hv) Q =
          -P.selectedDistinguishedClass TF hv := by
  obtain ⟨R, rfl⟩ := (P.localTorsionEquiv TF (P.sectFin_isBad TF hv)).surjective Q
  have h := P.canonical_iff_rankOneClass TF hv R
  rw [← (P.selectedGraphQuotientEquiv TF hv).injective.eq_iff,
    ← (P.selectedGraphQuotientEquiv TF hv).injective.eq_iff] at h
  simpa only [selectedGraphQuotientEquiv_class, map_neg, localTorsionEquiv_apply,
    selectedDistinguishedClass, TateFamily.IsCanonicalAt, coe_localTorsionMap] using h

/-- The image of the fixed second basis vector is itself a canonical local generator. -/
theorem selected_e₂_isCanonical :
    (TF.S (P.sectFin TF v) (P.sectFin_isBad TF hv)).IsCanonical P.ℓ
      (P.localTorsionMap (P.sectFin TF v) P.e₂) := by
  apply (P.selectedCanonical_iff_class TF hv _).mpr
  exact Or.inl rfl

end
end JoshiTeich.ReferenceIut.AdmissiblePrimeData

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut NumberField
open scoped Classical

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

universe u
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The seed's fixed second basis vector is canonical along its constructed section. -/
theorem valuationSection_e₂_isCanonical (S : InitialThetaGeometrySeed AG TG)
    {v : FinitePlace ↥(fieldOfModuli S.F S.E)} (hv : v ∈ S.VBad) :
    S.tate.IsCanonicalAt (S.valuationSection.sectFin v)
      ⟨v, hv, S.prime.sectFin_liesOver S.tate v⟩
      (S.prime.e₂ : S.prime.EK.toAffine.Point) :=
  S.prime.selected_e₂_isCanonical S.tate hv

end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
