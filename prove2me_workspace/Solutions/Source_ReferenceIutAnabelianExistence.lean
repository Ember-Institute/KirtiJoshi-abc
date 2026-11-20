/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Anabelian/Existence.lean
-/
import Solutions.Source_ReferenceIutInitialThetaData
import Solutions.Source_ReferenceIutOrbicurveData
import Solutions.Source_ReferenceIutTemperedModel

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open NumberField WeierstrassCurve OrbicurveDataSection
open JoshiTeich.ReferenceIut.Anabelian (Orbicurve EtalePi1Theory pointMap pointMap_injective)
open scoped Classical Valued

universe u

noncomputable section

attribute [local instance 1100] JoshiTeich.ReferenceIut.AdmissiblePrimeData.instDecidableEqK

private abbrev toJoshiTateFamily {F : Type u} [Field F] [NumberField F]
    {E : WeierstrassCurve F} [E.IsElliptic] {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
    {K : IntermediateField F Fbar} [NumberField ↥K] {ℓ : ℕ}
    {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} (TF : TateFamily E K ℓ VBad) :
    JoshiTeich.ReferenceIut.TateFamily E K ℓ VBad where
  S w hw :=
    let S := TF.S w hw
    { t := ⟨S.t.q, S.t.norm_lt_one⟩
      C := S.C
      hC := S.hC
      iso := S.iso
      iso_x := S.iso_x
      iso_y := S.iso_y }
  graphLine_galPlace := TF.graphLine_galPlace
  isCanonical_galPlace := TF.isCanonical_galPlace

section Scene1

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
  {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
  {VBad : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F E))}
  (J : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad)
  [NumberField ↥J.torsionField]
  (U : JoshiTeich.ReferenceIut.TateFamily E J.torsionField J.ℓ VBad)
  (v : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F E))

private abbrev completionEmbedding :=
  JoshiTeich.ReferenceIut.emb J.torsionField (J.sectFin U v)

private lemma selectedLine_map (hv : v ∈ VBad) :
    J.M.map (pointMap J.EK (completionEmbedding J U v)) =
      (U.S (J.sectFin U v) (J.sectFin_isBad U hv)).graphLine J.ℓ := by
  have h := congrArg
    (fun L : AddSubgroup J.EK.toAffine.Point => L.map (pointMap J.EK (completionEmbedding J U v)))
    (J.sectFin_graphLine U hv).symm
  exact h.trans (U.map_graphLineAt J (J.sectFin_isBad U hv))

private lemma selectedLine_card :
    Nat.card (J.M.map (pointMap J.EK (completionEmbedding J U v))) = J.ℓ :=
  (Nat.card_congr (AddSubgroup.equivMapOfInjective J.M _
    (pointMap_injective J.EK (completionEmbedding J U v))).toEquiv).symm.trans J.card_M

private abbrev cuspOrbicurve : Orbicurve ↥J.torsionField where
  E := J.EK
  isElliptic := (show (E.map (algebraMap F ↥J.torsionField)).IsElliptic from inferInstance)
  level := J.ℓ
  M := J.M
  pm := true

private lemma selectedCusp (hv : v ∈ VBad)
    (S : TateStructure (JoshiTeich.ReferenceIut.curveKw E J.torsionField (J.sectFin U v)))
    (hS : ∀ Q, S.IsCanonical J.ℓ Q ↔
      (U.S (J.sectFin U v) (J.sectFin_isBad U hv)).IsCanonical J.ℓ Q) :
    let X := cuspOrbicurve J
    let f := completionEmbedding J U v
    X.cuspBaseChange f (X.cuspOf J.distinguishedClass) =
      canonicalGraphCusp (X.baseChange f) S := by
  intro X f
  rw [Orbicurve.cuspBaseChange_cuspOf]
  let localTate : TateStructure (X.baseChange f).E := S
  have hex : ∃ Q : ↥(X.baseChange f).torsion, localTate.IsCanonical (X.baseChange f).level Q.1 := by
    refine ⟨X.mapTorsion f J.e₂, ?_⟩
    exact (hS _).mpr (J.selected_e₂_isCanonical U hv)
  have cusp_eq : canonicalGraphCusp (X.baseChange f) localTate =
      (X.baseChange f).cuspOf ((X.baseChange f).toQ hex.choose) :=
    dif_pos hex
  refine Eq.trans ?_ cusp_eq.symm
  let w := J.sectFin U v
  let hw := J.sectFin_isBad U hv
  obtain ⟨R, hRT, hR⟩ := U.exists_toLocal_eq J hw hex.choose.2
  have hRc : U.IsCanonicalAt w hw R := by
    change (U.S w hw).IsCanonical J.ℓ (JoshiTeich.ReferenceIut.TateFamily.toLocal J w R)
    exact hR.symm ▸ (hS _).mp hex.choose_spec
  have hclass := (J.canonical_iff_rankOneClass U hv ⟨R, hRT⟩).mp hRc
  have hchoose : hex.choose = X.mapTorsion f ⟨R, hRT⟩ :=
    Subtype.ext (hR.symm.trans (X.coe_mapTorsion f ⟨R, hRT⟩).symm)
  rw [hchoose, ← Orbicurve.mapQ_toQ]
  rcases hclass with h | h
  · change X.toQ ⟨R, hRT⟩ = J.distinguishedClass at h
    rw [h]
  · change X.toQ ⟨R, hRT⟩ = -J.distinguishedClass at h
    rw [h, map_neg, Orbicurve.cuspOf_neg _ rfl]

end Scene1

/-- The orbicurve and local witnesses for IUT I, Definition 3.1(d)–(f), using the same model
and Tate family as the P7 construction. -/
theorem anabelianExistence (Pi1 : EtalePi1Theory.{u}) (T : TemperedPi1Theory Pi1) :
    AnabelianExistence (modelAG Pi1) (modelTG Pi1 T) where
  exists_data F _ _ E _ Fbar _ _ _ VBad P _ TF _ hcore := by
    letI : Algebra ↥(fieldOfModuli F E) ↥P.torsionField :=
      (fieldOfModuli F E).instAlgebraSubtypeMem
    haveI : Algebra.IsIntegral ↥P.torsionField Fbar := by
      haveI : Algebra.IsAlgebraic F Fbar := IsAlgClosure.isAlgebraic
      exact (Algebra.IsAlgebraic.tower_top (K := F) ↥P.torsionField).isIntegral
    let VBad' : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F E)) := VBad
    let J : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad' := P.toJoshi
    letI : NumberField ↥J.torsionField := by
      change NumberField ↥P.torsionField
      infer_instance
    let U : JoshiTeich.ReferenceIut.TateFamily E J.torsionField J.ℓ VBad' := toJoshiTateFamily TF
    let S := J.sect U
    let O := orbicurveData P Pi1 hcore
    have localType (v : FinitePlace ↥(fieldOfModuli F E)) (hv : v ∈ VBad) :
        (modelAG Pi1).IsTypeOneZModPM P.ℓ (localize (S.sectFin v) O.XKu)
          (TF.S (S.sectFin v) (J.sectFin_isBad U hv)) :=
      let v' : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F E) := v
      let hv' : v' ∈ VBad' := hv
      ⟨J.ℓ_prime, rfl, selectedLine_map J U v' hv', selectedLine_card J U v'⟩
    refine ⟨O, ⟨{
      sect := ⟨S.sectFin, S.sectInf, S.sectFin_liesOver, S.sectInf_liesOver⟩
      local_diagram_cartesian := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      decomp := JoshiTeich.ReferenceIut.decompGroup ↥P.torsionField Fbar
      decomp_isClosed := JoshiTeich.ReferenceIut.decompGroup_isClosed ↥P.torsionField Fbar
      tateX := fun v hv => TF.S (S.sectFin v) (J.sectFin_isBad U hv)
      tateC := fun v hv => TF.S (S.sectFin v) (J.sectFin_isBad U hv)
      bad_type := localType
      bad_theta_model := localType
      epsilon_graph := ?_ }⟩⟩
    intro v hv
    let v' : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F E) := v
    let hv' : v' ∈ VBad' := hv
    exact selectedCusp J U v' hv'
      (TF.S (J.sectFin U v') (J.sectFin_isBad U hv')) (fun _ => Iff.rfl)

end
end AbcAdaptation.Reference.Iut.Anabelian
