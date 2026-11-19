/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/CyclicLocal.lean and Iut/Tripod/CyclicTorsion.lean

The decomposition-group argument applies the prime-order calculation to both stable lines.
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.TateTorsion
import Solutions.Source_SL2ImageLocalTorsion
import Solutions.Source_TripodCyclicBoundOdd
import Solutions.Source_TripodCyclicDecomposition
import Solutions.Source_TripodCyclicPrimeSubgroups

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

open NumberField WeierstrassCurve
open scoped Classical Valued

universe u

noncomputable section

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

attribute [local instance 1100] JoshiTeich.ReferenceIut.instDecidableEqIntermediateField

open JoshiTeich.ReferenceIut (galK)

private lemma bcK_galK (σ : C.Fbar ≃ₐ[C.F] C.Fbar) (P : R.EK.toAffine.Point) :
    R.bcK (galK C.E R.torsionField (AlgEquiv.restrictNormalHom R.torsionField σ) P) =
      galPointMap C.F C.E C.Fbar σ (R.bcK P) := by
  change (Affine.baseChange C.E ↥R.torsionField).Point at P
  change Affine.Point.map (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)
    (Affine.Point.map (W' := C.E) (S := C.F)
      (AlgEquiv.restrictNormalHom R.torsionField σ : ↥R.torsionField →ₐ[C.F] ↥R.torsionField) P) =
    Affine.Point.map (W' := C.E) (S := C.F) σ.toAlgHom
      (Affine.Point.map (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar) P)
  rw [Affine.Point.map_map, Affine.Point.map_map]
  have h : (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar).comp
      (AlgEquiv.restrictNormalHom R.torsionField σ : ↥R.torsionField →ₐ[C.F] ↥R.torsionField) =
      σ.toAlgHom.comp (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar) := by
    ext a
    exact AlgEquiv.restrictNormalHom_apply R.torsionField σ a
  rw [h]

private lemma galK_mem_comap_bcK (σ : ↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
    {H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar))}
    (hgal : ∀ τ : C.Fbar ≃ₐ[C.F] C.Fbar, ∀ P ∈ H, galPointMap C.F C.E C.Fbar τ P ∈ H)
    {P : R.EK.toAffine.Point} (hP : P ∈ H.comap R.bcK) :
    galK C.E R.torsionField σ P ∈ H.comap R.bcK := by
  obtain ⟨τ, rfl⟩ :=
    (AlgEquiv.restrictNormalHom_surjective (F := C.F) (K₁ := ↥R.torsionField) C.Fbar) σ
  rw [AddSubgroup.mem_comap, R.bcK_galK]
  exact hgal τ _ hP

private lemma eq_one_of_galK_fixed_torsion (σ : ↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
    (h : ∀ P ∈ R.TK, galK C.E R.torsionField σ P = P) : σ = 1 := by
  obtain ⟨τ, rfl⟩ :=
    (AlgEquiv.restrictNormalHom_surjective (F := C.F) (K₁ := ↥R.torsionField) C.Fbar) σ
  have hfix : ∀ Q : ↥(TFbar C ℓ), galPointMap C.F C.E C.Fbar τ Q.1 = Q.1 := by
    intro Q
    obtain ⟨P, hP⟩ := R.exists_bcK_eq Q.1 Q.2
    rw [← hP, ← R.bcK_galK, h P (R.mem_TK_of_bcK (hP ▸ Q.2))]
  have hrep : R.rep τ = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨Q, rfl⟩ := R.torsionBasis.surjective v
    rw [Matrix.toLin'_apply, ← R.rep_spec τ Q, Matrix.toLin'_one, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (hfix Q)
  have hτ : τ ∈ (AlgEquiv.restrictNormalHom R.torsionField).ker := by
    rw [R.restrictNormalHom_ker_eq]
    exact MonoidHom.mem_ker.mpr hrep
  exact MonoidHom.mem_ker.mp hτ

private lemma galK_eq_self_of_pow_eq_one (hℓ : ℓ.Prime)
    (σ : ↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) (hσ : σ ^ ℓ = 1)
    {a : R.EK.toAffine.Point} (ha : addOrderOf a = ℓ)
    (hstab : galK C.E R.torsionField σ a ∈ AddSubgroup.zmultiples a) :
    galK C.E R.torsionField σ a = a := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hstab
  have hiter (n : ℕ) : galK C.E R.torsionField (σ ^ n) a = m ^ n • a := by
    induction n with
    | zero =>
      have h1 : galK C.E R.torsionField 1 a = a := by cases a <;> rfl
      rw [pow_zero, pow_zero, one_smul, h1]
    | succ n ih =>
      have hmul : galK C.E R.torsionField (σ ^ n * σ) a =
          galK C.E R.torsionField (σ ^ n) (galK C.E R.torsionField σ a) := by
        cases a <;> rfl
      rw [pow_succ, hmul, ← hm, map_zsmul, ih, smul_smul, pow_succ, mul_comm]
  have hpow := hiter ℓ
  have hone : galK C.E R.torsionField 1 a = a := by cases a <;> rfl
  rw [hσ, hone] at hpow
  have hzero : (m ^ ℓ - 1) • a = 0 := by rw [sub_smul, one_smul, ← hpow, sub_self]
  have hdvd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hzero
  rw [ha] at hdvd
  have hmod := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  push_cast at hmod
  rw [ZMod.pow_card] at hmod
  have hdiff := (ZMod.intCast_zmod_eq_zero_iff_dvd (m - 1) ℓ).mp (by push_cast; exact hmod)
  have hfixed : (m - 1) • a = 0 :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mp (by rwa [ha])
  rw [← hm]
  calc
    m • a = (m - 1) • a + a := by rw [sub_smul, one_smul, sub_add_cancel]
    _ = a := by rw [hfixed, zero_add]

section GraphLine

variable {w : FinitePlace ↥R.torsionField}
variable (TF : JoshiTeich.ReferenceIut.TateFamily C.E R.torsionField ℓ C.VBadOdd)
variable (hw : JoshiTeich.ReferenceIut.IsBadPlace C.E R.torsionField C.VBadOdd w)

private lemma card_graphLineAt_and_le (hℓ : ℓ.Prime) :
    Nat.card (TF.graphLineAt w hw) = ℓ ∧ TF.graphLineAt w hw ≤ R.TK := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let f := JoshiTeich.ReferenceIut.Anabelian.pointMap R.EK
    (JoshiTeich.ReferenceIut.emb R.torsionField w)
  let S := TF.S w hw
  let T := JoshiTeich.ReferenceIut.TateStructure.torsion ℓ
    (JoshiTeich.ReferenceIut.curveKw C.E R.torsionField w)
  haveI : Finite ↥T := S.finite_torsion ℓ
  have hcard : ℓ * ℓ ≤ Nat.card ↥T := C.card_torsion_curveKw_ge R w
  have hf : Function.Injective f := JoshiTeich.ReferenceIut.Anabelian.pointMap_injective _ _
  have htorsion : R.TK.map f = T := by
    refine AddSubgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro Q ⟨P, hP, rfl⟩
      rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
        AddSubgroup.torsionBy.nsmul_iff.mp hP, map_zero]
    · rw [← Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ hf).toEquiv,
        R.card_torsionBy_EK, sq]
      exact S.card_torsion_le ℓ
  have hmap : (TF.graphLineAt w hw).map f = S.graphLine ℓ := by
    ext Q
    constructor
    · rintro ⟨P, hP, rfl⟩
      exact hP
    · intro hQ
      have hQT : Q ∈ T := S.graphLine_le_torsion ℓ hQ
      rw [← htorsion] at hQT
      obtain ⟨P, -, rfl⟩ := hQT
      exact ⟨P, hQ, rfl⟩
  constructor
  · rw [Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ hf).toEquiv, hmap]
    exact S.card_graphLine_eq ℓ hcard
  · intro P hP
    have hfP : f P ∈ T := S.graphLine_le_torsion ℓ hP
    rw [AddSubgroup.torsionBy.nsmul_iff] at hfP ⊢
    apply hf
    rw [map_nsmul, hfP, map_zero]

include TF in
private lemma prime_dvd_ramificationIdx_at_oddPlace (hℓ : ℓ.Prime)
    (hP2 : ¬ ℓ ∣ C.tateInputs.qOrder (AbcAdaptation.Tripod.placeUnder w)
      (C.placeUnder_mem_badAll_of_isBadPlace _ hw)) :
    ℓ ∣ (AbcAdaptation.Tripod.placeUnder (k := C.F) w).maximalIdeal.asIdeal.ramificationIdx'
      w.maximalIdeal.asIdeal := by
  let S₀ := TF.S w hw
  let S : TateStructure (curveKw C.E R.torsionField w) :=
    { t := ⟨S₀.t.q, S₀.t.norm_lt_one⟩
      C := S₀.C
      hC := S₀.hC
      iso := S₀.iso
      iso_x := S₀.iso_x
      iso_y := S₀.iso_y }
  exact C.prime_dvd_ramificationIdx_of_tateStructure R C.tateInputs hℓ
    (C.placeUnder_mem_badAll_of_isBadPlace _ hw) hP2 (AbcAdaptation.Tripod.liesOver_placeUnder w) S

/-- Under (P2), the Galois-stable subgroup of order ℓ is the graph line at each odd place. -/
theorem comap_bcK_eq_graphLineAt (hℓ : ℓ.Prime)
    {H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar))}
    (hH : Nat.card H = ℓ)
    (hgal : ∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∀ P ∈ H, galPointMap C.F C.E C.Fbar σ P ∈ H)
    (hP2 : ¬ ℓ ∣ C.tateInputs.qOrder (AbcAdaptation.Tripod.placeUnder w)
      (C.placeUnder_mem_badAll_of_isBadPlace _ hw)) :
    H.comap R.bcK = TF.graphLineAt w hw := by
  let HK := H.comap R.bcK
  let G := TF.graphLineAt w hw
  have hHle : H ≤ TFbar C ℓ := by
    intro Q hQ
    have h := card_nsmul_eq_zero' (x := (⟨Q, hQ⟩ : H))
    rw [hH] at h
    exact AddSubgroup.torsionBy.nsmul_iff.mpr (congrArg Subtype.val h)
  have hHKle : HK ≤ R.TK := fun P hP => R.mem_TK_of_bcK (hHle hP)
  have hHK : Nat.card HK = ℓ := by
    have hrange : H ≤ R.bcK.range := fun Q hQ => R.exists_bcK_eq Q (hHle hQ)
    have hmap : HK.map R.bcK = H := AddSubgroup.map_comap_eq_self hrange
    rw [Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ R.bcK_injective).toEquiv, hmap, hH]
  obtain ⟨hG, hGle⟩ := R.card_graphLineAt_and_le TF hw hℓ
  by_contra hne
  have hInf := addSubgroup_inf_eq_bot_of_card_prime hℓ hHK hG hne
  haveI : Finite R.TK :=
    Nat.finite_of_card_ne_zero (by rw [R.card_torsionBy_EK]; exact pow_ne_zero 2 hℓ.ne_zero)
  have hSup := addSubgroup_sup_eq_of_inf_eq_bot hHK hG
    (by rw [R.card_torsionBy_EK, sq]) hHKle hGle hInf
  have hram := R.prime_dvd_ramificationIdx_at_oddPlace TF hw hℓ hP2
  obtain ⟨σ, hfixPlace, hord⟩ :=
    exists_orderOf_eq_of_dvd_ramificationIdx (AbcAdaptation.Tripod.liesOver_placeUnder w) hℓ hram
  have hpow : σ ^ ℓ = 1 :=
    (congrArg (fun n : ℕ => σ ^ n) hord).symm.trans (pow_orderOf_eq_one σ)
  have hGmap : G.map (galK C.E R.torsionField σ) = G := by
    let hwσ := JoshiTeich.ReferenceIut.isBadPlace_galPlace C.E R.torsionField C.VBadOdd hw σ
    have h := TF.graphLine_galPlace w hw σ
    change TF.graphLineAt (JoshiTeich.ReferenceIut.galPlace σ w) hwσ = G.map _ at h
    have heq : ∀ {w' : FinitePlace ↥R.torsionField}
        (he : JoshiTeich.ReferenceIut.galPlace σ w = w')
        (hw' : JoshiTeich.ReferenceIut.IsBadPlace C.E R.torsionField C.VBadOdd w'),
        TF.graphLineAt (JoshiTeich.ReferenceIut.galPlace σ w) hwσ = TF.graphLineAt w' hw' := by
      intro w' he hw'
      subst w'
      rfl
    rw [heq hfixPlace hw] at h
    exact h.symm
  have hfixLine (A : AddSubgroup R.EK.toAffine.Point) (hA : Nat.card A = ℓ)
      (hstab : ∀ P ∈ A, galK C.E R.torsionField σ P ∈ A) :
      ∀ P ∈ A, galK C.E R.torsionField σ P = P := by
    intro P hP
    by_cases hP0 : P = 0
    · rw [hP0, map_zero]
    have hPorder := addOrderOf_eq_of_mem_of_card_prime hℓ hA hP hP0
    apply R.galK_eq_self_of_pow_eq_one hℓ σ hpow hPorder
    rw [zmultiples_eq_of_mem_of_card_prime hℓ hA hP hP0]
    exact hstab P hP
  have hfixHK := hfixLine HK hHK (fun P hP => R.galK_mem_comap_bcK σ hgal hP)
  have hfixG := hfixLine G hG (fun P hP => by
    rw [← hGmap]
    exact AddSubgroup.mem_map_of_mem _ hP)
  have hfix : ∀ P ∈ R.TK, galK C.E R.torsionField σ P = P := by
    intro P hP
    rw [← hSup] at hP
    obtain ⟨A, hA, B, hB, rfl⟩ := AddSubgroup.mem_sup.mp hP
    rw [map_add, hfixHK A hA, hfixG B hB]
  rw [R.eq_one_of_galK_fixed_torsion σ hfix, orderOf_one] at hord
  exact hℓ.one_lt.ne hord

end GraphLine

end

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

theorem cyclicLocalGraphLine_from_source (P : CurveProviders) : CyclicLocalGraphLineHyp P := by
  intro x ℓ hℓ hodd H hH hgal
  dsimp only
  intro w hw hP2
  letI : NumberField (P.curve x).F := (P.curve x).numberFieldF
  let R : (P.curve x).ModEllRepData ℓ := P.modRep x ℓ hℓ
  exact R.comap_bcK_eq_graphLineAt (R.tateFamilyOdd hℓ hodd) hw hℓ hH hgal hP2

/-- The global isogeny estimate supplies the cyclic field of the Tripod curve facts. -/
theorem curveFacts_of_cyclicMainBound (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {C₀ : ℝ} (hmain : CyclicMainBoundHyp P K C₀) :
    CurveFactsProp P K d (cyclicConst K C₀) :=
  ⟨cyclicBoundOdd_of_isogeny P K d (cyclicLocalGraphLine_from_source P) hmain⟩

end AbcAdaptation.Tripod
