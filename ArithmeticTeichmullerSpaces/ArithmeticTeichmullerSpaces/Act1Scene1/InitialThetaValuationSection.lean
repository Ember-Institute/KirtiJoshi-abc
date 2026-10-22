/-
original-path: `refer/iut/Iut/Anabelian/Existence.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `a36b42b9a221e1baaf434bb76c85b3a0dfbf33a7`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: source file retains the iut contributors' 2026 Apache-2.0 notice;
reviewed against `refer/iut/LICENSE` before copying.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(e)-(f); IUT IV Corollary 2.2, proof (P7);
Joshi III `ss:theta-data-fixing2` (the valuation section).
fidelity: extracted torsion-line and place-selection proofs only; added exact canonical-coset
comparison and a consumer on InitialThetaGeometrySeed. No model geometry copied.
boundary: Scene1/Derived; genuine orbicurve existence remains open.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Linear
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.LocalInputs
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlacesOver
import ArithmeticTeichmullerSpaces.Act1Scene1.ProducerContracts
import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlacesOver
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadPlaceFiniteness

/-!
The section is constructed from the same arithmetic torsion field and Tate family
as the producer seed. The SL2 argument aligns every bad-place graph line and its
canonical quotient generators with the fixed global torsion basis. This proof
does not use `modelAG`, `modelTG`, or an anabelian existence hypothesis.
The global covering diagram, core, and theta-root interpretation are separate
remaining obligations of `InitialThetaGeometryProducer`.
-/
namespace JoshiTeich.ReferenceIut.AdmissiblePrimeData

universe u

open WeierstrassCurve NumberField JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian OrbicurveDataSection
open scoped Classical

noncomputable section

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad)
variable [NumberField ↥P.torsionField]

attribute [local instance 1100] instDecidableEqK

/-- `ℓ` is prime. -/
local instance instFactPrime : Fact P.ℓ.Prime := ⟨P.ℓ_prime⟩

/-! ## The chosen line and cusp -/

/-- The first basis vector `e₁ ∈ E(K)[ℓ]`. -/
def e₁ : ↥P.TK := P.basisK.symm (Pi.single 0 1)

/-- The second basis vector `e₂ ∈ E(K)[ℓ]`. -/
def e₂ : ↥P.TK := P.basisK.symm (Pi.single 1 1)

/-- **The line `M = ⟨e₁⟩ ⊆ E(K)[ℓ]`** defining `C̲_K`. -/
def M : AddSubgroup P.EK.toAffine.Point := AddSubgroup.zmultiples (P.e₁ : P.EK.toAffine.Point)

/-- The line `⟨(1, 0)⟩ ⊆ 𝔽_ℓ²`. -/
def M₀ : AddSubgroup (Fin 2 → ZMod P.ℓ) := AddSubgroup.zmultiples (Pi.single 0 1)

lemma fact_prime : Fact P.ℓ.Prime := ⟨P.ℓ_prime⟩

/-- The image in `𝔽_ℓ²` of a subgroup of `E(K)[ℓ]`. -/
def toV (L : AddSubgroup P.EK.toAffine.Point) : AddSubgroup (Fin 2 → ZMod P.ℓ) :=
  (L.addSubgroupOf P.TK).map P.basisK.toAddMonoidHom

lemma mem_toV_iff (L : AddSubgroup P.EK.toAffine.Point) (R : ↥P.TK) :
    P.basisK R ∈ P.toV L ↔ (R : P.EK.toAffine.Point) ∈ L := by
  unfold toV
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨S, hS, hSR⟩
    have : S = R := P.basisK.injective hSR
    subst this
    exact (AddSubgroup.mem_addSubgroupOf).mp hS
  · intro h
    exact ⟨R, (AddSubgroup.mem_addSubgroupOf).mpr h, rfl⟩

lemma toV_injective {L L' : AddSubgroup P.EK.toAffine.Point} (hL : L ≤ P.TK) (hL' : L' ≤ P.TK)
    (h : P.toV L = P.toV L') : L = L' := by
  ext R
  constructor
  · intro hR
    have hRT : R ∈ P.TK := hL hR
    have := (P.mem_toV_iff L ⟨R, hRT⟩).mpr hR
    rw [h] at this
    exact (P.mem_toV_iff L' ⟨R, hRT⟩).mp this
  · intro hR
    have hRT : R ∈ P.TK := hL' hR
    have := (P.mem_toV_iff L' ⟨R, hRT⟩).mpr hR
    rw [← h] at this
    exact (P.mem_toV_iff L ⟨R, hRT⟩).mp this

lemma card_toV {L : AddSubgroup P.EK.toAffine.Point} (hL : L ≤ P.TK) :
    Nat.card (P.toV L) = Nat.card L := by
  unfold toV
  rw [Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ P.basisK.injective).symm.toEquiv,
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hL).toEquiv]

lemma toV_map_galK (σ : Fbar ≃ₐ[F] Fbar) {L : AddSubgroup P.EK.toAffine.Point}
    (hL : L ≤ P.TK) :
    P.toV (L.map (P.galK (P.restrictK σ))) =
      (P.toV L).map (mulVecHom (P.rep σ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ))) := by
  ext v
  constructor
  · intro hv
    unfold toV at hv
    rw [AddSubgroup.mem_map] at hv
    obtain ⟨S, hS, rfl⟩ := hv
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map] at hS
    obtain ⟨R, hR, hRS⟩ := hS
    have hRT : R ∈ P.TK := hL hR
    have hS' : S = P.galTK (P.restrictK σ) ⟨R, hRT⟩ := Subtype.ext hRS.symm
    rw [AddSubgroup.mem_map]
    refine ⟨P.basisK ⟨R, hRT⟩, (P.mem_toV_iff L ⟨R, hRT⟩).mpr hR, ?_⟩
    rw [mulVecHom_apply, ← P.basisK_galTK, hS']
    rfl
  · intro hv
    rw [AddSubgroup.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    unfold toV at hu
    rw [AddSubgroup.mem_map] at hu
    obtain ⟨R, hR, rfl⟩ := hu
    rw [AddSubgroup.mem_addSubgroupOf] at hR
    rw [mulVecHom_apply]
    change (P.rep σ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)).mulVec (P.basisK R) ∈ _
    rw [← P.basisK_galTK]
    exact (P.mem_toV_iff _ _).mpr (AddSubgroup.mem_map_of_mem _ hR)

lemma e₁_ne_zero : (P.e₁ : P.EK.toAffine.Point) ≠ 0 := by
  haveI := P.fact_prime
  intro h
  have h1 : P.e₁ = 0 := Subtype.ext h
  have := congrArg P.basisK h1
  simp only [e₁, AddEquiv.apply_symm_apply, map_zero] at this
  have := congrFun this 0
  simp at this

lemma e₁_mem_TK : (P.e₁ : P.EK.toAffine.Point) ∈ P.TK := P.e₁.2

lemma M_le_TK : P.M ≤ P.TK := (AddSubgroup.zmultiples_le).mpr P.e₁_mem_TK

lemma card_M : Nat.card P.M = P.ℓ := by
  haveI := P.fact_prime
  unfold M
  rw [Nat.card_zmultiples]
  refine addOrderOf_eq_prime ?_ P.e₁_ne_zero
  exact (AddSubgroup.torsionBy.nsmul_iff).mp P.e₁_mem_TK

lemma toV_M : P.toV P.M = P.M₀ := by
  ext v
  unfold toV M M₀
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨S, hS, rfl⟩
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff] at hS
    obtain ⟨n, hn⟩ := hS
    have : S = n • P.e₁ := Subtype.ext hn.symm
    rw [this, map_zsmul]
    simp only [e₁, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
  · intro hv
    rw [AddSubgroup.mem_zmultiples_iff] at hv
    obtain ⟨n, rfl⟩ := hv
    refine ⟨n • P.e₁, ?_, ?_⟩
    · rw [AddSubgroup.mem_addSubgroupOf]
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
    · simp only [map_zsmul, e₁, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]

lemma card_M₀ : Nat.card P.M₀ = P.ℓ := by
  rw [← P.toV_M, P.card_toV P.M_le_TK, P.card_M]

lemma e₂_not_mem_M : (P.e₂ : P.EK.toAffine.Point) ∉ P.M := by
  haveI := P.fact_prime
  intro h
  have := (P.mem_toV_iff P.M P.e₂).mpr h
  rw [P.toV_M] at this
  simp only [e₂, AddEquiv.apply_symm_apply, M₀] at this
  rw [AddSubgroup.mem_zmultiples_iff] at this
  obtain ⟨n, hn⟩ := this
  have := congrFun hn 1
  simp at this

lemma single_one_not_mem_M₀ : (Pi.single 1 1 : Fin 2 → ZMod P.ℓ) ∉ P.M₀ := by
  have := P.e₂_not_mem_M
  rwa [← P.mem_toV_iff P.M P.e₂, P.toV_M, e₂, AddEquiv.apply_symm_apply] at this

/-! ## The choice of places -/

variable (TF : TateFamily E P.torsionField P.ℓ VBad)

lemma map_map_symm (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField)
    (R : (Affine.baseChange E ↥P.torsionField).Point) :
    Affine.Point.map (W' := E) (S := F) (σ : ↥P.torsionField →ₐ[F] ↥P.torsionField)
      (Affine.Point.map (W' := E) (S := F) (σ.symm : ↥P.torsionField →ₐ[F] ↥P.torsionField) R) =
      R := by
  rw [Affine.Point.map_map]
  have : (σ : ↥P.torsionField →ₐ[F] ↥P.torsionField).comp
      (σ.symm : ↥P.torsionField →ₐ[F] ↥P.torsionField) = AlgHom.id F ↥P.torsionField := by
    ext x; simp
  rw [this]
  exact Affine.Point.map_id R

lemma galK_galK_symm (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField) (R : P.EK.toAffine.Point) :
    P.galK σ (P.galK σ.symm R) = R :=
  P.map_map_symm σ R

lemma galK_eq (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField) :
    JoshiTeich.ReferenceIut.galK E P.torsionField σ = P.galK σ := rfl

/-- **The good place over `v ∈ V_mod^bad`**: a place at which the graph line is `M` and the
canonical generators are `±e₂ (mod M)`. -/
theorem exists_good_place {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) :
    ∃ w : FinitePlace ↥P.torsionField, ∃ hwv : FinitePlace.LiesOver w v,
      TF.graphLineAt w ⟨v, hv, hwv⟩ = P.M ∧
      ∀ R, TF.IsCanonicalAt w ⟨v, hv, hwv⟩ R → (R - P.e₂ ∈ P.M ∨ R + P.e₂ ∈ P.M) := by
  haveI := P.fact_prime
  obtain ⟨w₀, hw₀⟩ := FinitePlace.exists_liesOver (K := ↥P.torsionField) v
  have hb₀ : IsBadPlace E P.torsionField VBad w₀ := ⟨v, hv, hw₀⟩
  have hL₀le := TF.graphLineAt_le_TK P hb₀
  have hL₀card := TF.card_graphLineAt P hb₀
  obtain ⟨g₀, hg₀T, hg₀L, hg₀⟩ := TF.exists_canonical P hb₀
  have hcardV : Nat.card (P.toV (TF.graphLineAt w₀ hb₀)) = P.ℓ := by
    rw [P.card_toV hL₀le, hL₀card]
  have hgV : P.basisK ⟨g₀, hg₀T⟩ ∉ P.toV (TF.graphLineAt w₀ hb₀) := fun h =>
    hg₀L ((P.mem_toV_iff _ _).mp h)
  obtain ⟨A, hAL, hAg⟩ := exists_sl2 (P.toV (TF.graphLineAt w₀ hb₀)) P.M₀ hcardV P.card_M₀ hgV
    P.single_one_not_mem_M₀
  obtain ⟨τ, hτ⟩ := P.sl_le_range A
  set σ := P.restrictK τ with hσ
  have hA : (P.rep τ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)) = A := by
    rw [hτ]; rfl
  have hwv : FinitePlace.LiesOver (galPlace σ w₀) v := galPlace_liesOver (fun _ => rfl) σ hw₀
  have hb : IsBadPlace E P.torsionField VBad (galPlace σ w₀) := ⟨v, hv, hwv⟩
  have hgl : TF.graphLineAt (galPlace σ w₀) hb = (TF.graphLineAt w₀ hb₀).map (P.galK σ) :=
    TF.graphLine_galPlace w₀ hb₀ σ
  have hLM : (TF.graphLineAt w₀ hb₀).map (P.galK σ) = P.M := by
    apply P.toV_injective (by
      rintro _ ⟨R, hR, rfl⟩
      exact P.galK_mem_TK σ (hL₀le hR)) P.M_le_TK
    rw [hσ, P.toV_map_galK τ hL₀le, hA, hAL, P.toV_M]
  refine ⟨galPlace σ w₀, hwv, hgl.trans hLM, ?_⟩
  intro R hR
  have hR₀ : TF.IsCanonicalAt w₀ hb₀ (P.galK σ.symm R) := by
    have h := TF.isCanonical_galPlace w₀ hb₀ σ (P.galK σ.symm R)
    rw [galK_eq, P.galK_galK_symm] at h
    exact h.mp hR
  -- `σ g₀ ≡ e₂ (mod M)`
  have hσg : P.galK σ g₀ - P.e₂ ∈ P.M := by
    have h1 : P.basisK (P.galTK σ ⟨g₀, hg₀T⟩ - P.e₂) ∈ P.M₀ := by
      rw [map_sub, hσ, P.basisK_galTK, hA, e₂, AddEquiv.apply_symm_apply]
      exact hAg
    rw [← P.toV_M] at h1
    have h2 := (P.mem_toV_iff P.M _).mp h1
    simpa using h2
  rcases (hg₀ _).mp hR₀ with h | h
  · left
    have := AddSubgroup.mem_map_of_mem (P.galK σ) h
    rw [map_sub, P.galK_galK_symm, hLM] at this
    have := P.M.add_mem this hσg
    rwa [sub_add_sub_cancel] at this
  · right
    have := AddSubgroup.mem_map_of_mem (P.galK σ) h
    rw [map_add, P.galK_galK_symm, hLM] at this
    have h3 := P.M.sub_mem this hσg
    have h4 : R + P.galK σ g₀ - (P.galK σ g₀ - P.e₂) = R + P.e₂ := by abel
    rwa [h4] at h3

/-- The chosen finite place of `K` over a finite place of `F_mod`. -/
def sectFin (v : FinitePlace ↥(fieldOfModuli F E)) : FinitePlace ↥P.torsionField :=
  if hv : v ∈ VBad then (P.exists_good_place TF hv).choose
  else (FinitePlace.exists_liesOver (K := ↥P.torsionField) v).choose

lemma sectFin_liesOver (v : FinitePlace ↥(fieldOfModuli F E)) :
    FinitePlace.LiesOver (P.sectFin TF v) v := by
  unfold sectFin
  split_ifs with hv
  · exact (P.exists_good_place TF hv).choose_spec.choose
  · exact (FinitePlace.exists_liesOver (K := ↥P.torsionField) v).choose_spec

lemma sectFin_isBad {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) :
    IsBadPlace E P.torsionField VBad (P.sectFin TF v) :=
  ⟨v, hv, P.sectFin_liesOver TF v⟩

lemma sectFin_eq {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) :
    P.sectFin TF v = (P.exists_good_place TF hv).choose := by
  unfold sectFin
  rw [dite_eq_left hv]

lemma _root_.JoshiTeich.ReferenceIut.TateFamily.graphLineAt_congr {w w' : FinitePlace ↥P.torsionField} (h : w = w')
    (hw : IsBadPlace E P.torsionField VBad w) (hw' : IsBadPlace E P.torsionField VBad w') :
    TF.graphLineAt w hw = TF.graphLineAt w' hw' := by
  subst h
  rfl

lemma _root_.JoshiTeich.ReferenceIut.TateFamily.isCanonicalAt_congr {w w' : FinitePlace ↥P.torsionField} (h : w = w')
    (hw : IsBadPlace E P.torsionField VBad w) (hw' : IsBadPlace E P.torsionField VBad w')
    (R : P.EK.toAffine.Point) : TF.IsCanonicalAt w hw R ↔ TF.IsCanonicalAt w' hw' R := by
  subst h
  exact Iff.rfl

lemma sectFin_graphLine {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) :
    TF.graphLineAt (P.sectFin TF v) (P.sectFin_isBad TF hv) = P.M :=
  (TF.graphLineAt_congr P (P.sectFin_eq TF hv) _ _).trans
    (P.exists_good_place TF hv).choose_spec.choose_spec.1

lemma sectFin_canonical {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) (R)
    (hR : TF.IsCanonicalAt (P.sectFin TF v) (P.sectFin_isBad TF hv) R) :
    R - P.e₂ ∈ P.M ∨ R + P.e₂ ∈ P.M :=
  (P.exists_good_place TF hv).choose_spec.choose_spec.2 R
    ((TF.isCanonicalAt_congr P (P.sectFin_eq TF hv) _ _ R).mp hR)

/-- **The valuation section `V ⊆ V(K)`** (IUT I, Definition 3.1(e)). -/
def sect : ValuationSection F E Fbar VBad P where
  sectFin := P.sectFin TF
  sectInf v := (InfinitePlace.exists_liesOver (K := ↥P.torsionField) v).choose
  sectFin_liesOver := P.sectFin_liesOver TF
  sectInf_liesOver v := (InfinitePlace.exists_liesOver (K := ↥P.torsionField) v).choose_spec


/-- Exact canonical cosets at the selected place, in the global torsion basis. -/
lemma sectFin_canonical_iff {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad)
    (R : P.EK.toAffine.Point) :
    TF.IsCanonicalAt (P.sectFin TF v) (P.sectFin_isBad TF hv) R ↔
      R - P.e₂ ∈ P.M ∨ R + P.e₂ ∈ P.M := by
  constructor
  · exact P.sectFin_canonical TF hv R
  · intro hR
    obtain ⟨g, -, -, hg⟩ := TF.exists_canonical P (P.sectFin_isBad TF hv)
    have hgc : TF.IsCanonicalAt (P.sectFin TF v) (P.sectFin_isBad TF hv) g :=
      (hg g).mpr (Or.inl (by simp))
    have hgm := P.sectFin_canonical TF hv g hgc
    apply (hg R).mpr
    rw [P.sectFin_graphLine TF hv]
    rcases hR with hR | hR <;> rcases hgm with hgm | hgm
    · exact Or.inl (by convert P.M.sub_mem hR hgm using 1; abel)
    · exact Or.inr (by convert P.M.add_mem hR hgm using 1; abel)
    · exact Or.inr (by convert P.M.add_mem hR hgm using 1; abel)
    · exact Or.inl (by convert P.M.sub_mem hR hgm using 1; abel)

end
end JoshiTeich.ReferenceIut.AdmissiblePrimeData

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut NumberField
open scoped Classical

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

universe u
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The seed's scalar tower pins the moduli-field algebra to the canonical one. -/
theorem algebraModK_eq_canonical (S : InitialThetaGeometrySeed AG TG) :
    S.algebraModK = (fieldOfModuli S.F S.E).instAlgebraSubtypeMem := by
  apply Algebra.algebra_ext
  intro x
  apply Subtype.ext
  exact congrArg Subtype.val
    (@IsScalarTower.algebraMap_apply
      (↥(fieldOfModuli S.F S.E)) S.F ↥S.prime.torsionField
      _ _ _ _ _ S.algebraModK S.towerModK x)

/-- The actual valuation-section component constructed from the producer's seed. -/
noncomputable def valuationSection (S : InitialThetaGeometrySeed AG TG) :
    ValuationSection S.F S.E S.Fbar S.VBad S.prime where
  sectFin := S.prime.sectFin S.tate
  sectInf v := (InfinitePlace.exists_liesOver (K := ↥S.prime.torsionField) v).choose
  sectFin_liesOver v := S.algebraModK_eq_canonical.symm ▸
    S.prime.sectFin_liesOver S.tate v
  sectInf_liesOver v :=
    (InfinitePlace.exists_liesOver (K := ↥S.prime.torsionField) v).choose_spec

/-- The seed's chosen finite-place section is injective: a place is determined by
its contraction to the field of moduli. -/
theorem valuationSection_sectFin_injective (S : InitialThetaGeometrySeed AG TG) :
    Function.Injective S.valuationSection.sectFin := by
  intro v₁ v₂ h
  have hv₁ := S.valuationSection.sectFin_liesOver v₁
  have hv₂ := S.valuationSection.sectFin_liesOver v₂
  calc
    v₁ = iutPlaceUnder (F := ↥(fieldOfModuli S.F S.E))
        (Kt := ↥S.prime.torsionField) (S.valuationSection.sectFin v₁) :=
      iutPlaceUnder_eq_of_liesOver hv₁
    _ = iutPlaceUnder (F := ↥(fieldOfModuli S.F S.E))
        (Kt := ↥S.prime.torsionField) (S.valuationSection.sectFin v₂) :=
      congrArg (iutPlaceUnder (F := ↥(fieldOfModuli S.F S.E))
        (Kt := ↥S.prime.torsionField)) h
    _ = v₂ := (iutPlaceUnder_eq_of_liesOver hv₂).symm

/-- The actual representative of a moduli place contracted to the arithmetic
field `S.F` through the seed's selected torsion-field place. -/
noncomputable def valuationSection_contractedPlace
    (S : InitialThetaGeometrySeed AG TG)
    (v : NumberField.FinitePlace ↥(fieldOfModuli S.F S.E)) :
    NumberField.FinitePlace S.F :=
  iutPlaceUnder (F := S.F) (S.valuationSection.sectFin v)

theorem valuationSection_contractedPlace_liesOver
    (S : InitialThetaGeometrySeed AG TG)
    (v : NumberField.FinitePlace ↥(fieldOfModuli S.F S.E)) :
    FinitePlace.LiesOver (S.valuationSection_contractedPlace v) v := by
  have hsect := S.valuationSection.sectFin_liesOver v
  have hcontract := iutPlaceUnder_liesOver
    (F := S.F) (Kt := ↥S.prime.torsionField)
    (S.valuationSection.sectFin v)
  haveI : (S.valuationSection.sectFin v).maximalIdeal.asIdeal.LiesOver
      v.maximalIdeal.asIdeal := hsect
  haveI : (S.valuationSection.sectFin v).maximalIdeal.asIdeal.LiesOver
      (S.valuationSection_contractedPlace v).maximalIdeal.asIdeal := hcontract
  exact Ideal.LiesOver.tower_bot (S.valuationSection.sectFin v).maximalIdeal.asIdeal
    (S.valuationSection_contractedPlace v).maximalIdeal.asIdeal v.maximalIdeal.asIdeal

theorem valuationSection_contractedPlace_injective
    (S : InitialThetaGeometrySeed AG TG) :
    Function.Injective S.valuationSection_contractedPlace := by
  intro v₁ v₂ h
  have hv₁ : v₁ = iutPlaceUnder
      (F := ↥(fieldOfModuli S.F S.E))
      (S.valuationSection_contractedPlace v₁) :=
    iutPlaceUnder_eq_of_liesOver (S.valuationSection_contractedPlace_liesOver v₁)
  have hv₂ : v₂ = iutPlaceUnder
      (F := ↥(fieldOfModuli S.F S.E))
      (S.valuationSection_contractedPlace v₂) :=
    iutPlaceUnder_eq_of_liesOver (S.valuationSection_contractedPlace_liesOver v₂)
  calc
    v₁ = iutPlaceUnder (F := ↥(fieldOfModuli S.F S.E))
        (S.valuationSection_contractedPlace v₁) := hv₁
    _ = iutPlaceUnder (F := ↥(fieldOfModuli S.F S.E))
        (S.valuationSection_contractedPlace v₂) := congrArg _ h
    _ = v₂ := hv₂.symm

theorem valuationSection_vbad_finite (S : InitialThetaGeometrySeed AG TG) :
    S.VBad.Finite := by
  let g : NumberField.FinitePlace S.F →
      NumberField.FinitePlace ↥(fieldOfModuli S.F S.E) := fun w =>
    iutPlaceUnder (F := ↥(fieldOfModuli S.F S.E)) w
  have hfinite : (g '' {w : NumberField.FinitePlace S.F |
      HasMultiplicativeReductionAt S.E w}).Finite :=
    (JoshiTeich.Act1Scene1.multiplicativeReductionPlaces_finite S.E).image g
  refine hfinite.subset ?_
  intro v hv
  let wF := S.valuationSection_contractedPlace v
  have hbv := S.valuationSection_contractedPlace_liesOver v
  have hgb : v = g wF := iutPlaceUnder_eq_of_liesOver hbv
  have hmult : HasMultiplicativeReductionAt S.E wF :=
    S.global.bad_multiplicative v hv wF hbv
  refine ⟨wF, hmult, ?_⟩
  exact hgb.symm

theorem valuationSection_vbad_image_subset_badPlacesOver
    (S : InitialThetaGeometrySeed AG TG) :
    S.valuationSection.sectFin '' S.VBad ⊆
      iutBadPlacesOver (S.VBad : Set (NumberField.FinitePlace
        ↥(fieldOfModuli S.F S.E))) := by
  rintro w ⟨v, hv, rfl⟩
  exact ⟨v, hv, S.valuationSection.sectFin_liesOver v⟩

theorem valuationSection_vbad_image_finite
    (S : InitialThetaGeometrySeed AG TG) :
    (S.valuationSection.sectFin '' S.VBad).Finite :=
  S.valuationSection_vbad_finite.image _

/-- The chosen section aligns the seed's actual Tate graph line globally. -/
theorem valuationSection_graphLine (S : InitialThetaGeometrySeed AG TG)
    {v : FinitePlace ↥(fieldOfModuli S.F S.E)} (hv : v ∈ S.VBad) :
    S.tate.graphLineAt (S.valuationSection.sectFin v)
      ⟨v, hv, S.prime.sectFin_liesOver S.tate v⟩ = S.prime.M :=
  S.prime.sectFin_graphLine S.tate hv

/-- The same section aligns canonical Tate generators, with both signs retained. -/
theorem valuationSection_canonical_iff (S : InitialThetaGeometrySeed AG TG)
    {v : FinitePlace ↥(fieldOfModuli S.F S.E)} (hv : v ∈ S.VBad)
    (R : S.prime.EK.toAffine.Point) :
    S.tate.IsCanonicalAt (S.valuationSection.sectFin v)
      ⟨v, hv, S.prime.sectFin_liesOver S.tate v⟩ R ↔
      R - (S.prime.e₂ : S.prime.EK.toAffine.Point) ∈ S.prime.M ∨
        R + (S.prime.e₂ : S.prime.EK.toAffine.Point) ∈ S.prime.M :=
  S.prime.sectFin_canonical_iff S.tate hv R

end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
