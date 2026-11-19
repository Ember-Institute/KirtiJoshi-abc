/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/CyclicTorsion.lean, Iut/Tripod/CyclicBound.lean
               and Iut/Tripod/CyclicIsogeny.lean
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.TateFamilyOfTorsion
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TatePoleOrder
import Solutions.Source_ModEllRepGalois
import Solutions.Source_ReferenceIutTateLocalModels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve
open scoped Classical

universe u

namespace LocalHeightData

variable (L : LocalHeightData)

noncomputable def heightOn (s : L.ι → Prop) : ℝ :=
  (∑ v ∈ L.bad.filter s, (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

lemma heightOn_nonneg (s : L.ι → Prop) : 0 ≤ L.heightOn s := by
  unfold heightOn
  refine div_nonneg (Finset.sum_nonneg fun v hv => ?_) (Nat.cast_nonneg _)
  have hp := (L.p_prime v (Finset.mem_filter.mp hv).1).one_lt.le
  have hlog : 0 ≤ Real.log (L.p v) := Real.log_nonneg (by exact_mod_cast hp)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hlog

lemma height_eq_heightOn_add (s : L.ι → Prop) :
    L.height = L.heightOn s + L.heightOn (fun v => ¬ s v) := by
  unfold height heightOn
  rw [← add_div, Finset.sum_filter_add_sum_filter_not]

lemma heightEq_eq_heightOn (q : ℕ) :
    L.heightEq q = L.heightOn (fun v => L.p v = q) := by
  unfold heightEq heightOn
  congr 1
  exact Finset.sum_congr (by ext v; simp only [Finset.mem_filter]) fun _ _ => rfl

lemma height_sub_heightEq_two :
    L.height - L.heightEq 2 = L.heightOn (fun v => L.p v ≠ 2) := by
  have hsplit := L.height_eq_heightOn_add (fun v => L.p v = 2)
  rw [← L.heightEq_eq_heightOn] at hsplit
  linarith

end LocalHeightData

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

/-- The odd places of the moduli field below the multiplicative places of the curve. -/
def VBadOdd : Set (FinitePlace ↥(fieldOfModuli C.F C.E)) :=
  {v | residueChar v ≠ 2 ∧ (∃ w : FinitePlace C.F, FinitePlace.LiesOver w v) ∧
    ∀ w : FinitePlace C.F, FinitePlace.LiesOver w v → HasMultiplicativeReductionAt C.E w}

lemma placeUnder_mem_badAll_of_isBadPlace
    (K : IntermediateField C.F C.Fbar) [NumberField ↥K] {w : FinitePlace ↥K}
    (hw : JoshiTeich.ReferenceIut.IsBadPlace C.E K C.VBadOdd w) :
    (AbcAdaptation.Tripod.placeUnder w : FinitePlace C.F) ∈ C.badAll :=
  mult_placeUnder C.E K (fun _ hv v hvw => hv.2.2 v hvw) hw

namespace ModEllRepData

variable {C} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

local instance (priority := 1100) instDecidableEqOddTorsionField :
    DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- The Galois-equivariant Tate family at all odd multiplicative places. -/
noncomputable def tateFamilyOdd (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    JoshiTeich.ReferenceIut.TateFamily C.E R.torsionField ℓ C.VBadOdd :=
  JoshiTeich.ReferenceIut.tateFamilyOfTorsion C.E R.torsionField ℓ (VBad := C.VBadOdd)
    (fun _ hv => hv.1) (fun _ hv v hvw => hv.2.2 v hvw)
    hℓ hodd R.TK le_rfl (by rw [R.card_torsionBy_EK, sq])

end ModEllRepData

end EllipticCurveData

end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField WeierstrassCurve
open scoped Classical Real

section LocalHeight

variable (P : CurveProviders) (x : Pt)

private lemma localData_hv_eq {v : FinitePlace (P.curve x).F} (hv : v ∈ (P.curve x).badAll) :
    (P.localData x).hv v = (P.tate x).qOrder v hv := by
  change (if h : v ∈ (P.curve x).badAll then (P.tate x).qOrder v h else 0) = _
  rw [dif_pos hv]

/-- The odd part of the height, multiplied by the field degree, is the sum of local logarithms of j. -/
lemma finrank_mul_h_sub :
    (Module.finrank ℚ (P.curve x).F : ℝ) * (P.h x - (P.localData x).heightEq 2) =
      ∑ v ∈ (P.localData x).bad.filter (fun v => (P.localData x).p v ≠ 2),
        Real.log ((show FinitePlace (P.curve x).F from v) (P.curve x).E.j) := by
  change (Module.finrank ℚ (P.curve x).F : ℝ) *
      ((P.localData x).height - (P.localData x).heightEq 2) = _
  rw [(P.localData x).height_sub_heightEq_two]
  unfold LocalHeightData.heightOn
  have hdeg : ((P.localData x).deg : ℝ) = Module.finrank ℚ (P.curve x).F := rfl
  have hdeg0 : (Module.finrank ℚ (P.curve x).F : ℝ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  rw [hdeg, mul_div_cancel₀ _ hdeg0]
  refine Finset.sum_congr (by ext v; simp only [Finset.mem_filter]) fun v hv => ?_
  have hv' : v ∈ (P.curve x).badAll :=
    (P.arith x).badAll_finite.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hposLog := posLog_j_eq_of_mem_badAll P x hv'
  have hterm : 0 < ((P.tate x).qOrder v hv' : ℝ) * inertDeg (P.curve x).F v *
      Real.log (residueChar v) := by
    have hq := (P.tate x).qOrder_pos v hv'
    have hf := (P.arith x).inertDeg_pos v
    have hp : (1 : ℝ) < residueChar v := by exact_mod_cast (residueChar_prime v).one_lt
    exact mul_pos (mul_pos (by exact_mod_cast hq) (by exact_mod_cast hf)) (Real.log_pos hp)
  have hlog : 0 < Real.log ((show FinitePlace (P.curve x).F from v) (P.curve x).E.j) := by
    rw [← hposLog, Real.posLog_apply] at hterm
    exact (lt_max_iff.mp hterm).resolve_left (lt_irrefl 0)
  change ((P.localData x).hv v : ℝ) * inertDeg (P.curve x).F v * Real.log (residueChar v) = _
  rw [localData_hv_eq P x hv', ← hposLog, Real.posLog_apply, max_eq_right hlog.le]

end LocalHeight

/-- The cyclic subgroup pulls back to the graph line at every odd multiplicative place. -/
def IsGraphLineOdd (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))) : Prop :=
  letI : NumberField (P.curve x).F := (P.curve x).numberFieldF
  let R : (P.curve x).ModEllRepData ℓ := P.modRep x ℓ hℓ
  letI := JoshiTeich.ReferenceIut.instDecidableEqIntermediateField R.torsionField
  ∀ (w : FinitePlace ↥R.torsionField)
    (hw : JoshiTeich.ReferenceIut.IsBadPlace (P.curve x).E R.torsionField
      (P.curve x).VBadOdd w),
    H.comap R.bcK = (R.tateFamilyOdd hℓ hodd).graphLineAt w hw

/-- The constant in the cyclic bound for a choice of the archimedean torsion constant C₀. -/
noncomputable def cyclicConst (K : CompactlyBounded) (C₀ : ℝ) : ℝ :=
  (2 * Real.log (32 * C₀) + 6 * K.c + 4 * Real.log 4) / 6

/-- The local graph-line result of Iut.Tripod.CyclicLocal on the provider curve. -/
def CyclicLocalGraphLineHyp (P : CurveProviders) : Prop :=
  ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))),
    Nat.card H = ℓ →
    (∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H) →
    letI : NumberField (P.curve x).F := (P.curve x).numberFieldF
    let R : (P.curve x).ModEllRepData ℓ := P.modRep x ℓ hℓ
    letI := JoshiTeich.ReferenceIut.instDecidableEqIntermediateField R.torsionField
    ∀ (w : FinitePlace ↥R.torsionField)
      (hw : JoshiTeich.ReferenceIut.IsBadPlace (P.curve x).E R.torsionField
        (P.curve x).VBadOdd w),
      (¬ ℓ ∣ (P.tate x).qOrder (placeUnder (k := (P.curve x).F) w)
        ((P.curve x).placeUnder_mem_badAll_of_isBadPlace R.torsionField hw)) →
      H.comap R.bcK = (R.tateFamilyOdd hℓ hodd).graphLineAt w hw

/-- The Vélu estimate of Iut.Tripod.Cyclic.main_bound with its archimedean constant fixed. -/
def CyclicMainBoundHyp (P : CurveProviders) (K : CompactlyBounded) (C₀ : ℝ) : Prop :=
  ∀ x ∈ K.set, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))),
    Nat.card H = ℓ →
    (∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H) →
    IsGraphLineOdd P x hℓ hodd H →
    ((ℓ : ℝ) - 1) / 4 * (P.h x - (P.localData x).heightEq 2) ≤
      10 * Real.log ℓ + (2 * Real.log (32 * C₀) + 6 * K.c + 4 * Real.log 4)

/-- The local graph-line result and the Vélu estimate give the cyclic bound used by CurveFactsProp. -/
theorem cyclicBoundOdd_of_isogeny (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {C₀ : ℝ} (hlocal : CyclicLocalGraphLineHyp P) (hmain : CyclicMainBoundHyp P K C₀) :
    CyclicBoundOddHyp P K d (cyclicConst K C₀) := by
  intro x hx ℓ hℓ h7 hP2 hcyc
  obtain ⟨H, hH, hgal⟩ := hcyc
  have hodd : ℓ ≠ 2 := by omega
  have hgraph : IsGraphLineOdd P x hℓ hodd H := by
    let R : (P.curve x).ModEllRepData ℓ := P.modRep x ℓ hℓ
    intro w hw
    have hv := (P.curve x).placeUnder_mem_badAll_of_isBadPlace R.torsionField hw
    have hP2' := hP2 _ ((P.arith x).badAll_finite.mem_toFinset.mpr hv)
    rw [localData_hv_eq P x hv] at hP2'
    exact hlocal x ℓ hℓ hodd H hH hgal w hw hP2'
  have hbound := hmain x hx.1 ℓ hℓ hodd H hH hgal hgraph
  have hX : 0 ≤ P.h x - (P.localData x).heightEq 2 := by
    change 0 ≤ (P.localData x).height - (P.localData x).heightEq 2
    rw [(P.localData x).height_sub_heightEq_two]
    exact (P.localData x).heightOn_nonneg _
  have hlog : 0 ≤ Real.log ℓ := Real.log_nonneg (by exact_mod_cast hℓ.one_lt.le)
  have hcoeff : ((ℓ : ℝ) - 2) / 24 ≤ ((ℓ : ℝ) - 1) / 24 := by linarith
  calc
    _ ≤ ((ℓ : ℝ) - 1) / 24 * (P.h x - (P.localData x).heightEq 2) :=
      mul_le_mul_of_nonneg_right hcoeff hX
    _ = (((ℓ : ℝ) - 1) / 4 * (P.h x - (P.localData x).heightEq 2)) / 6 := by ring
    _ ≤ (10 * Real.log ℓ + (2 * Real.log (32 * C₀) + 6 * K.c + 4 * Real.log 4)) / 6 :=
      div_le_div_of_nonneg_right hbound (by norm_num)
    _ ≤ 2 * Real.log ℓ + cyclicConst K C₀ := by
      unfold cyclicConst
      linarith

end AbcAdaptation.Tripod

end
