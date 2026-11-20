/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Anabelian/Existence.lean
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaTorsionQuotient
import Solutions.Source_TripodCoreModel

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve
open scoped Classical

universe u

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
  {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
  {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

private theorem toJoshiUniformizer {K : Type*} [NormedField K] {π : K}
    (h : AbcAdaptation.Reference.TateCurvesTheta.IsUniformizer π) :
    _root_.TateCurvesTheta.IsUniformizer π :=
  ⟨h.ne_zero, h.norm_lt_one, h.generates⟩

/-- The same admissible prime, representation, and Tate parameters in the Scene1 reference
library. Its torsion field is the same fixed field. -/
noncomputable abbrev AdmissiblePrimeData.toJoshi (P : AdmissiblePrimeData F E Fbar VBad) :
    JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad where
  ℓ := P.ℓ
  ℓ_prime := P.ℓ_prime
  five_le := P.five_le
  torsionBasis := P.torsionBasis
  rep := P.rep
  rep_spec := P.rep_spec
  sl_le_range := P.sl_le_range
  ker_isOpen := P.ker_isOpen
  galois_deg_prime := P.galois_deg_prime
  residueChar_coprime := P.residueChar_coprime
  tate w hw := ⟨(P.tate w hw).q, (P.tate w hw).norm_lt_one⟩
  tateJ_eq := P.tateJ_eq
  unif := P.unif
  unif_isUniformizer w hw := toJoshiUniformizer (P.unif_isUniformizer w hw)
  q_order_coprime w hw := by
    let t := P.tate w hw
    let h := P.unif_isUniformizer w hw
    let t' : _root_.TateCurvesTheta.TateParameter (localCompletion w) := ⟨t.q, t.norm_lt_one⟩
    have hord : t'.orderZ (toJoshiUniformizer h) = t.orderZ h :=
      t'.orderZ_eq_of_norm (toJoshiUniformizer h) (t.norm_q_eq_zpow h)
    change Nat.Coprime P.ℓ (t'.orderZ (toJoshiUniformizer h)).toNat
    rw [hord]
    exact P.q_order_coprime w hw

namespace Anabelian

open JoshiTeich.ReferenceIut.Anabelian (Orbicurve EtalePi1Theory)
open OrbicurveDataSection

attribute [local instance 1100] JoshiTeich.ReferenceIut.AdmissiblePrimeData.instDecidableEqK

noncomputable section

variable [IsAlgClosure F Fbar]

section Orbicurve

variable {VBad' : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F E))}
variable (J : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad')

private abbrev modelCKu : Orbicurve ↥J.torsionField where
  E := J.EK
  isElliptic := (show (E.map (algebraMap F ↥J.torsionField)).IsElliptic from inferInstance)
  level := J.ℓ
  M := J.M
  pm := true

private abbrev modelXKu : Orbicurve ↥J.torsionField := { modelCKu J with pm := false }

private abbrev modelXK : Orbicurve ↥J.torsionField :=
  (Orbicurve.oncePunctured E).baseChange (algebraMap F ↥J.torsionField)

private abbrev modelCK : Orbicurve ↥J.torsionField :=
  (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).baseChange (algebraMap F ↥J.torsionField)

variable [NumberField ↥J.torsionField]

private lemma modelLine_nsmul_mem (R : J.EK.toAffine.Point)
    (hR : R ∈ J.M) (S : AddSubgroup J.EK.toAffine.Point) : J.ℓ • R ∈ S := by
  have hT : R ∈ J.TK := J.M_le_TK hR
  have hzero : J.ℓ • R = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hT
  exact hzero.symm ▸ S.zero_mem

private def modelCoverXKuXK : Orbicurve.Cover (modelXKu J) (modelXK J) where
  E_eq := rfl
  n := J.ℓ
  n_pos := J.ℓ_prime.pos
  mul := mul_one _
  M_le R hR := modelLine_nsmul_mem J R hR _
  pm_le h := absurd h Bool.false_ne_true

private def modelCoverXKuCKu : Orbicurve.Cover (modelXKu J) (modelCKu J) where
  E_eq := rfl
  n := 1
  n_pos := Nat.one_pos
  mul := one_mul _
  M_le R hR := by
    change (1 : ℕ) • R ∈ J.M
    rwa [one_smul]
  pm_le _ := rfl

private def modelCoverXKCK : Orbicurve.Cover (modelXK J) (modelCK J) where
  E_eq := rfl
  n := 1
  n_pos := Nat.one_pos
  mul := one_mul _
  M_le R hR := by
    change (1 : ℕ) • R ∈ (modelCK J).M
    rw [one_smul]
    exact hR
  pm_le _ := rfl

private def modelCoverCKuCK : Orbicurve.Cover (modelCKu J) (modelCK J) where
  E_eq := rfl
  n := J.ℓ
  n_pos := J.ℓ_prime.pos
  mul := mul_one _
  M_le R hR := modelLine_nsmul_mem J R hR _
  pm_le _ := rfl

private def modelRankOneEquiv : J.rankOneQuotient ≃ ZMod J.ℓ :=
  J.rankOneEquiv.toEquiv

private theorem modelDistinguishedClass_nonzero :
    modelRankOneEquiv J J.distinguishedClass ≠ 0 := by
  letI : Fact J.ℓ.Prime := ⟨J.ℓ_prime⟩
  intro h
  exact one_ne_zero (J.rankOneEquiv_distinguishedClass.symm.trans h)

end Orbicurve

/-- The model covering diagram and its distinguished cusp on the torsion field. -/
def orbicurveData (P : AdmissiblePrimeData F E Fbar VBad) (Pi1 : EtalePi1Theory.{u})
    [NumberField ↥P.torsionField] (hcore : HasCoreUniversally (modelAG Pi1) F E) :
    OrbicurveData (modelAG Pi1) F E Fbar VBad P := by
  let J := P.toJoshi
  letI : NumberField ↥J.torsionField := by
    change NumberField ↥P.torsionField
    infer_instance
  exact
    { CKu := modelCKu J
      CKu_type := ⟨J.ℓ_prime, rfl, rfl, J.M_le_TK, J.card_M, J.card_TK⟩
      CKu_core := by
        have hXK := hcore ↥J.torsionField (algebraMap F ↥J.torsionField)
        have hCK := (Pi1.hasCore_iff_of_cover (modelCoverXKCK J)).mp hXK
        exact (Pi1.hasCore_iff_of_cover (modelCoverCKuCK J)).mpr hCK
      XKu := modelXKu J
      XKu_type := ⟨J.ℓ_prime, rfl, rfl, J.M_le_TK, J.card_M, J.card_TK⟩
      XKu_to_XK := modelCoverXKuXK J
      XKu_to_CKu := modelCoverXKuCKu J
      XK_to_CK := modelCoverXKCK J
      CKu_to_CK := modelCoverCKuCK J
      diagram_cartesian := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      QIso := modelRankOneEquiv J
      q := J.distinguishedClass
      q_ne_zero := modelDistinguishedClass_nonzero J
      epsilon := (modelCKu J).cuspOf J.distinguishedClass
      epsilon_spec := rfl }

end

end Anabelian
end AbcAdaptation.Reference.Iut
