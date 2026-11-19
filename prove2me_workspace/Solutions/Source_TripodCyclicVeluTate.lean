/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/CyclicIsogeny.lean (tate_bound and finite_tate) and
Iut/Tripod/CyclicTorsion.lean (exists_mem_VBadOdd)
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutVeluTateGain
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.BadPlaceNorm
import Solutions.Source_TripodCyclicBoundOdd
import Solutions.Source_TripodCyclicVeluDescent
import Solutions.Source_TripodRelativeAbsoluteValue

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Cyclic

open AbcAdaptation.Reference.Iut NumberField WeierstrassCurve
open JoshiTeich.Act1Scene1.IutCyclicTate (ratio_mul_bound)
open JoshiTeich.Act1Scene1.IutCyclicVelu (veluRatio)
open JoshiTeich.ReferenceIut (norm_two_eq_one_of_notMem two_notMem_of_isBadPlace)
open JoshiTeich.ReferenceIut.Anabelian (pointMap)
open scoped Classical Valued

attribute [local instance 1100] JoshiTeich.ReferenceIut.instDecidableEqIntermediateField

noncomputable section

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime)
variable (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar)))

local instance (priority := 1100) veluTateNumberField : NumberField ↥(L P x hℓ) :=
  (P.modRep x ℓ hℓ).numberField_torsionField

private lemma isBadPlace_of_liesOver {v : FinitePlace (P.curve x).F}
    (hv : v ∈ (P.curve x).badAll) (h₂ : residueChar v ≠ 2)
    {w : FinitePlace (L P x hℓ)} (hwv : FinitePlace.LiesOver w v) :
    JoshiTeich.ReferenceIut.IsBadPlace (P.curve x).E (L P x hℓ) (P.curve x).VBadOdd w := by
  let C := P.curve x
  let K := L P x hℓ
  have hbelow : ∃ v₀ : FinitePlace ↥(fieldOfModuli C.F C.E), FinitePlace.LiesOver v v₀ :=
    (P.arith x).exists_liesOver v
  obtain ⟨v₀, hvv₀⟩ := hbelow
  have hres : residueChar v = residueChar v₀ := (P.arith x).residueChar_liesOver v₀ v hvv₀
  have hv₀2 : residueChar v₀ ≠ 2 := fun h => h₂ (hres.trans h)
  have hv₀ : v₀ ∈ C.VBadOdd :=
    ⟨hv₀2, ⟨v, hvv₀⟩, fun u hu => (P.arith x).mult_invariant v₀ hv₀2 v u hvv₀ hu hv⟩
  letI : Algebra ↥(fieldOfModuli C.F C.E) ↥K :=
    (fieldOfModuli C.F C.E).instAlgebraSubtypeMem
  have hmap : algebraMap ↥(fieldOfModuli C.F C.E) ↥K =
      (algebraMap C.F ↥K).comp (algebraMap ↥(fieldOfModuli C.F C.E) C.F) :=
    RingHom.ext fun _ => rfl
  letI : IsScalarTower ↥(fieldOfModuli C.F C.E) C.F ↥K :=
    IsScalarTower.of_algebraMap_eq' hmap
  letI : IsScalarTower (𝓞 ↥(fieldOfModuli C.F C.E)) (𝓞 C.F) (𝓞 ↥K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hmap a)
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.LiesOver v₀.maximalIdeal.asIdeal := hvv₀
  exact ⟨v₀, hv₀, ⟨(Ideal.LiesOver.trans w.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal v₀.maximalIdeal.asIdeal).over⟩⟩

variable [Fintype (HL P x hℓ H)]

/-- The fourth power of the product of the two designated Vélu ratios is
bounded by the inverse absolute value of j to the power ℓ − 1 at an odd
multiplicative place of the torsion field. -/
theorem tate_bound (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2)
    (hgraph : IsGraphLineOdd P x hℓ hℓ2 H) (w : FinitePlace (L P x hℓ))
    (hw : JoshiTeich.ReferenceIut.IsBadPlace (P.curve x).E (L P x hℓ) (P.curve x).VBadOdd w) :
    (w (veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ)) *
        w (veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ))) ^ 4 *
      w (algebraMap (P.curve x).F (L P x hℓ) (P.curve x).E.j) ^ (ℓ - 1) ≤ 1 := by
  let TF := (P.modRep x ℓ hℓ).tateFamilyOdd hℓ hℓ2
  let φ := JoshiTeich.ReferenceIut.emb (L P x hℓ) w
  let W := WL P x hℓ
  letI : (P.curve x).E.IsElliptic := (P.curve x).isElliptic
  letI : W.IsElliptic := by
    change ((P.curve x).E.map (algebraMap (P.curve x).F (L P x hℓ))).IsElliptic
    infer_instance
  let S : JoshiTeich.ReferenceIut.TateStructure (W.map φ) := TF.S w hw
  let rankOne : (Valued.v : Valuation (JoshiTeich.ReferenceIut.localCompletion w)
      (WithZero (Multiplicative ℤ))).RankOne :=
    NumberField.HeightOneSpectrum.instRankOneAdicCompletion (L P x hℓ) w.maximalIdeal
  have hnorm (a : L P x hℓ) : ‖φ a‖ = w a := FinitePlace.norm_embedding_eq w a
  have hcard : Fintype.card (HL P x hℓ H) = ℓ :=
    (Fintype.card_eq_nat_card).trans (card_HL P x hℓ H hH)
  have h2 : ‖(2 : JoshiTeich.ReferenceIut.localCompletion w)‖ = 1 :=
    norm_two_eq_one_of_notMem
      (two_notMem_of_isBadPlace (P.curve x).E (L P x hℓ) (fun _ hv => hv.1) hw)
  have hline : HL P x hℓ H = TF.graphLineAt w hw := hgraph w hw
  have hgr : ∀ Q ∈ HL P x hℓ H, pointMap W φ Q ∈ S.graphLine ℓ := by
    intro Q hQ
    rw [hline] at hQ
    exact hQ
  have hmain := @ratio_mul_bound (JoshiTeich.ReferenceIut.localCompletion w)
    inferInstance inferInstance rankOne inferInstance
    (L P x hℓ) inferInstance φ W S (HL P x hℓ H) inferInstance
    ℓ (hℓ.odd_of_ne_two hℓ2) hcard h2 hgr
    (T₁ P x hℓ) (R₁ P x hℓ) (T₂ P x hℓ) (R₂ P x hℓ)
    (T₁_ne_zero P x hℓ) (T₁_add_self P x hℓ) (R₁_add_self P x hℓ)
    (T₂_ne_zero P x hℓ) (T₂_add_self P x hℓ) (R₂_add_self P x hℓ) (T₁_ne_T₂ P x hℓ)
  simp only [hnorm] at hmain
  have hJ : S.t.tateJ = φ (algebraMap (P.curve x).F (L P x hℓ) (P.curve x).E.j) := by
    calc
      S.t.tateJ = (S.C • W.map φ).j := by
        change S.t.tateCurve.c₄ ^ 3 / S.t.tateCurve.Δ = _
        rw [← S.hC, JoshiTeich.ReferenceIut.j_eq_inv_Δ_mul, div_eq_inv_mul]
      _ = (W.map φ).j := variableChange_j _ _
      _ = _ := by
        change (((P.curve x).E.map (algebraMap (P.curve x).F (L P x hℓ))).map
          φ).j = _
        rw [map_j, map_j]
  have hJnorm : w (algebraMap (P.curve x).F (L P x hℓ) (P.curve x).E.j) =
      ‖S.t.q.val‖⁻¹ := by
    simpa only [hJ, hnorm] using S.t.norm_tateJ (JoshiTeich.ReferenceIut.twelve_ne_zero w)
  have hj_nonneg : 0 ≤ w (algebraMap (P.curve x).F (L P x hℓ) (P.curve x).E.j) :=
    apply_nonneg w _
  calc
    _ ≤ ‖S.t.q.val‖ ^ (ℓ - 1) *
        w (algebraMap (P.curve x).F (L P x hℓ) (P.curve x).E.j) ^ (ℓ - 1) :=
      mul_le_mul_of_nonneg_right hmain (pow_nonneg hj_nonneg _)
    _ = 1 := by
      rw [← mul_pow, hJnorm, mul_inv_cancel₀ S.t.norm_q_pos.ne', one_pow]

/-- The Tate gain for the descended product of the two designated ratios at an
odd multiplicative place of the base field. -/
theorem finite_tate {ρ : (P.curve x).F}
    (hρ : algebraMap (P.curve x).F (L P x hℓ) ρ =
      veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
        veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ))
    (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (hgraph : IsGraphLineOdd P x hℓ hℓ2 H)
    {v : FinitePlace (P.curve x).F} (hv : v ∈ (P.curve x).badAll) (h₂ : residueChar v ≠ 2) :
    v ρ ^ 4 * v (P.curve x).E.j ^ (ℓ - 1) ≤ 1 := by
  obtain ⟨w, hwv⟩ := JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver (K := L P x hℓ) v
  have hw := isBadPlace_of_liesOver P x hℓ hv h₂ hwv
  have hb := tate_bound P x hℓ H hH hℓ2 hgraph w hw
  rw [← map_mul, ← hρ] at hb
  simp only [apply_algebraMap_eq_pow hwv] at hb
  have hpow : (v ρ ^ 4 * v (P.curve x).E.j ^ (ℓ - 1)) ^ relLocalDeg w v ≤
      1 ^ relLocalDeg w v := by
    rw [mul_pow, pow_right_comm (v ρ), pow_right_comm (v (P.curve x).E.j), one_pow]
    exact hb
  have hnonneg : 0 ≤ v ρ ^ 4 * v (P.curve x).E.j ^ (ℓ - 1) :=
    mul_nonneg (pow_nonneg (apply_nonneg v ρ) _) (pow_nonneg (apply_nonneg v _) _)
  exact (pow_le_pow_iff_left₀ hnonneg zero_le_one (relLocalDeg_ne_zero hwv)).mp hpow

end

end AbcAdaptation.Tripod.Cyclic
