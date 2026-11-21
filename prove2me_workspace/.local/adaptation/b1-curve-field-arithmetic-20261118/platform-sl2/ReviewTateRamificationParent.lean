import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit

/-
Proof of the selected-place ramification statement from a local Tate structure.
The following sections retain the notices on the adapted proof material.
-/
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.Basic
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateStructure
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply
import Definitions.Def_AbcAdaptation_Tripod_RelativeValuation
import Theorems.Thm_AbcAdaptation_Reference_Iut_nonempty_tateStructure_of_torsion

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/ModEllRepGalois.lean
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

open WeierstrassCurve Matrix
open scoped Classical

universe u

noncomputable section

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

local instance (priority := 1100) instDecidableEqTorsionField : DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- The curve over the torsion field `K`. -/
abbrev EK : WeierstrassCurve ↥R.torsionField :=
  C.E.map (algebraMap C.F ↥R.torsionField)

/-- Base change of points from `K` to the chosen algebraic closure. -/
def bcK : R.EK.toAffine.Point →+ Affine.Point (Affine.baseChange C.E C.Fbar) :=
  Affine.Point.map (W' := C.E) (S := C.F)
    (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)

lemma bcK_injective : Function.Injective R.bcK :=
  Affine.Point.map_injective (W' := C.E) (S := C.F)
    (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)

/-- The `ℓ`-torsion over `K`. -/
abbrev TK : AddSubgroup R.EK.toAffine.Point := AddSubgroup.torsionBy R.EK.toAffine.Point ℓ

/-- The `ℓ`-torsion over the chosen algebraic closure. -/
abbrev TFbar (C : EllipticCurveData.{u}) (ℓ : ℕ) :
    AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar)) :=
  AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ

lemma galPointMap_eq_of_mem_ker {σ : C.Fbar ≃ₐ[C.F] C.Fbar} (hσ : σ ∈ R.rep.ker)
    (Q : ↥(TFbar C ℓ)) : galPointMap C.F C.E C.Fbar σ Q.1 = Q.1 := by
  have h := R.rep_spec σ Q
  rw [MonoidHom.mem_ker.mp hσ] at h
  simp only [Units.val_one, Matrix.one_mulVec] at h
  exact congrArg Subtype.val (R.torsionBasis.injective h)

/-- Every geometric `ℓ`-torsion point comes from a point over `K`. -/
lemma exists_bcK_eq (Q : Affine.Point (Affine.baseChange C.E C.Fbar))
    (hQ : Q ∈ TFbar C ℓ) : ∃ P : R.EK.toAffine.Point, R.bcK P = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · have hfix : ∀ σ ∈ R.rep.ker, σ x = x ∧ σ y = y := by
      intro σ hσ
      have h' := R.galPointMap_eq_of_mem_ker hσ ⟨_, hQ⟩
      simp only [galPointMap, Affine.Point.map_some] at h'
      exact Affine.Point.some.inj h'
    have hx : x ∈ R.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).1
    have hy : y ∈ R.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).2
    have hns : (Affine.baseChange C.E ↥R.torsionField).Nonsingular
        (⟨x, hx⟩ : ↥R.torsionField) ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular (W := C.E)
        (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar).injective _ _).mp h
    exact ⟨.some _ _ hns, rfl⟩

lemma bcK_mem_TFbar {P : R.EK.toAffine.Point} (hP : P ∈ R.TK) : R.bcK P ∈ TFbar C ℓ := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

lemma mem_TK_of_bcK {P : R.EK.toAffine.Point} (hP : R.bcK P ∈ TFbar C ℓ) : P ∈ R.TK := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul] at hP
  exact R.bcK_injective (hP.trans (map_zero _).symm)

/-- Base change induces an additive equivalence on the `ℓ`-torsion. -/
def torsionEquiv : ↥R.TK ≃+ ↥(TFbar C ℓ) :=
  AddEquiv.ofBijective
    ((R.bcK.domRestrict R.TK).codRestrict (TFbar C ℓ) fun P => R.bcK_mem_TFbar P.2)
    ⟨fun P P' h => Subtype.ext (R.bcK_injective (congrArg Subtype.val h)),
     fun Q => by
      obtain ⟨P, hP⟩ := R.exists_bcK_eq Q.1 Q.2
      exact ⟨⟨P, R.mem_TK_of_bcK (hP ▸ Q.2)⟩, Subtype.ext hP⟩⟩

/-- The `ℓ`-torsion over `K` has cardinality `ℓ ^ 2`. -/
lemma card_torsionBy_EK : Nat.card R.TK = ℓ ^ 2 := by
  rw [Nat.card_congr (R.torsionEquiv.trans R.torsionBasis).toEquiv, Nat.card_pi, Nat.card_zmod]
  simp

end

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths: Iut/Anabelian/TateTorsion.lean and Iut/Cor312/ThetaData/TateStructure.lean
TateTorsion.lean source commit: 76c7866b5bbc4adbd245a30af1a4fd05d32f8c3f (Christian Merten)
Adaptation: use the existing Tate structure and graph line in the adaptation namespace.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.TateStructure

open WeierstrassCurve TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} (S : TateStructure E)

lemma ofUnit_eq_iff (u v : kˣ) :
    S.ofUnit u = S.ofUnit v ↔ ∃ n : ℤ, v = S.t.q ^ n * u := by
  unfold ofUnit
  rw [S.iso.injective.eq_iff, Additive.ofMul.injective.eq_iff, QuotientGroup.eq]
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, mul_comm, mul_inv_cancel_left]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, mul_comm (S.t.q ^ n) u, inv_mul_cancel_left]⟩

lemma ofUnit_surjective : Function.Surjective S.ofUnit := fun P => by
  obtain ⟨a, ha⟩ := S.iso.surjective P
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  exact ⟨u, by unfold ofUnit; rw [hu]; simpa using ha⟩

lemma q_zpow_injective : Function.Injective (fun n : ℤ => S.t.q ^ n) := by
  intro a b h
  have hnorm := congrArg (fun x : kˣ => ‖(x : k)‖) h
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow, norm_zpow] at hnorm
  exact zpow_right_injective₀ S.t.norm_q_pos S.t.norm_lt_one.ne hnorm

lemma ofUnit_eq_zero_iff (u : kˣ) : S.ofUnit u = 0 ↔ ∃ n : ℤ, u = S.t.q ^ n := by
  rw [← S.ofUnit_one, S.ofUnit_eq_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right hn.symm
  · rintro ⟨n, rfl⟩
    exact ⟨-n, by rw [zpow_neg, inv_mul_cancel]⟩

lemma nsmul_ofUnit (n : ℕ) (u : kˣ) : n • S.ofUnit u = S.ofUnit (u ^ n) := by
  unfold ofUnit
  rw [← map_nsmul]
  rfl

lemma ofUnit_mem_torsionBy_iff (ℓ : ℕ) (u : kˣ) :
    S.ofUnit u ∈ AddSubgroup.torsionBy E.toAffine.Point ℓ ↔ ∃ n : ℤ, u ^ ℓ = S.t.q ^ n := by
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_ofUnit, ofUnit_eq_zero_iff]

lemma expo_congr (ℓ : ℕ) {u v : kˣ} {n m : ℤ} (huv : S.ofUnit u = S.ofUnit v)
    (hu : u ^ ℓ = S.t.q ^ n) (hv : v ^ ℓ = S.t.q ^ m) : (m : ZMod ℓ) = n := by
  obtain ⟨j, hj⟩ := (S.ofUnit_eq_iff u v).mp huv
  have h : S.t.q ^ m = S.t.q ^ (j * ℓ + n) := by
    rw [← hv, hj, mul_pow, hu, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  have hm := S.q_zpow_injective h
  simp [hm, Int.cast_add, Int.cast_mul]

variable (ℓ : ℕ)

/-- The ℓ-torsion of `E(k)`. -/
abbrev torsion (E : WeierstrassCurve k) : AddSubgroup E.toAffine.Point :=
  AddSubgroup.torsionBy E.toAffine.Point ℓ

lemma exists_rep (P : ↥(torsion ℓ E)) :
    ∃ u : kˣ, S.ofUnit u = P ∧ ∃ n : ℤ, u ^ ℓ = S.t.q ^ n := by
  obtain ⟨u, hu⟩ := S.ofUnit_surjective P.1
  exact ⟨u, hu, (S.ofUnit_mem_torsionBy_iff ℓ u).mp (hu ▸ P.2)⟩

def rep (P : ↥(torsion ℓ E)) : kˣ := (S.exists_rep ℓ P).choose

lemma ofUnit_rep (P : ↥(torsion ℓ E)) : S.ofUnit (S.rep ℓ P) = P :=
  (S.exists_rep ℓ P).choose_spec.1

def expo (P : ↥(torsion ℓ E)) : ℤ := (S.exists_rep ℓ P).choose_spec.2.choose

lemma rep_pow (P : ↥(torsion ℓ E)) : S.rep ℓ P ^ ℓ = S.t.q ^ S.expo ℓ P :=
  (S.exists_rep ℓ P).choose_spec.2.choose_spec

/-- The residue homomorphism sends the class of `u` to `n` modulo `ℓ` when `u ^ ℓ = q ^ n`. -/
def resid : ↥(torsion ℓ E) →+ ZMod ℓ where
  toFun P := (S.expo ℓ P : ZMod ℓ)
  map_zero' := by
    obtain ⟨j, hj⟩ := (S.ofUnit_eq_zero_iff _).mp (S.ofUnit_rep ℓ 0)
    have h : S.t.q ^ S.expo ℓ 0 = S.t.q ^ (j * ℓ) := by
      rw [← S.rep_pow, hj, ← zpow_natCast, ← zpow_mul]
    have := S.q_zpow_injective h
    simp [this]
  map_add' P Q := by
    have h : S.ofUnit (S.rep ℓ (P + Q)) = S.ofUnit (S.rep ℓ P * S.rep ℓ Q) := by
      rw [ofUnit_mul, ofUnit_rep, ofUnit_rep, ofUnit_rep]
      rfl
    have := S.expo_congr ℓ h (S.rep_pow ℓ (P + Q))
      (by rw [mul_pow, rep_pow, rep_pow, ← zpow_add])
    simp only [Int.cast_add] at this
    exact this.symm

lemma resid_apply (P : ↥(torsion ℓ E)) : S.resid ℓ P = (S.expo ℓ P : ZMod ℓ) := rfl

lemma resid_eq_zero_iff (P : ↥(torsion ℓ E)) :
    S.resid ℓ P = 0 ↔ (P : E.toAffine.Point) ∈ S.graphLine ℓ := by
  constructor
  · intro h
    rw [resid_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨j, hj⟩ := h
    refine ⟨S.rep ℓ P * (S.t.q ^ j)⁻¹, ?_, ?_⟩
    · rw [mul_pow, rep_pow, hj, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm (j : ℤ),
        mul_inv_cancel]
    · rw [ofUnit_mul, ofUnit_rep, (S.ofUnit_eq_zero_iff (S.t.q ^ j)⁻¹).mpr ⟨-j, by rw [zpow_neg]⟩,
        add_zero]
  · rintro ⟨ζ, hζ, hζP⟩
    have := S.expo_congr ℓ (hζP.trans (S.ofUnit_rep ℓ P).symm) (by rw [hζ, zpow_zero])
      (S.rep_pow ℓ P)
    rw [resid_apply, this]
    simp

variable [NeZero ℓ]

lemma graphLine_le_torsion : S.graphLine ℓ ≤ torsion ℓ E := by
  rintro _ ⟨ζ, hζ, rfl⟩
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_ofUnit, hζ, ofUnit_one]

lemma ofUnit_rootsOfUnity_surjective :
    Function.Surjective (fun ζ : rootsOfUnity ℓ k =>
      (⟨S.ofUnit ζ.1, ⟨ζ.1, (mem_rootsOfUnity ℓ ζ.1).mp ζ.2, rfl⟩⟩ : ↥(S.graphLine ℓ))) := by
  rintro ⟨P, ζ, hζ, rfl⟩
  exact ⟨⟨ζ, (mem_rootsOfUnity ℓ ζ).mpr hζ⟩, rfl⟩

instance finite_graphLine : Finite ↥(S.graphLine ℓ) :=
  Finite.of_surjective _ (S.ofUnit_rootsOfUnity_surjective ℓ)

lemma card_graphLine_le : Nat.card ↥(S.graphLine ℓ) ≤ ℓ :=
  (Nat.card_le_card_of_surjective _ (S.ofUnit_rootsOfUnity_surjective ℓ)).trans
    (card_rootsOfUnity (R := k) (k := ℓ))

lemma resid_ker : (S.resid ℓ).ker = (S.graphLine ℓ).addSubgroupOf (torsion ℓ E) := by
  ext P
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, resid_eq_zero_iff]

lemma card_torsion_eq :
    Nat.card ↥(torsion ℓ E) = Nat.card ↥(S.graphLine ℓ) * Nat.card ↥(S.resid ℓ).range := by
  rw [← AddSubgroup.card_mul_index (S.resid ℓ).ker, AddSubgroup.index_ker, resid_ker]
  rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (S.graphLine_le_torsion ℓ)).toEquiv]

lemma card_range_le : Nat.card ↥(S.resid ℓ).range ≤ ℓ :=
  (Nat.card_le_card_of_injective _ Subtype.val_injective).trans (by rw [Nat.card_zmod])

include S in
theorem finite_torsion : Finite ↥(torsion ℓ E) := by
  apply Nat.finite_of_card_ne_zero
  rw [S.card_torsion_eq ℓ]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

lemma resid_range_eq_top (hcard : ℓ * ℓ ≤ Nat.card ↥(torsion ℓ E)) :
    (S.resid ℓ).range = ⊤ := by
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmod]
  apply Nat.le_antisymm (S.card_range_le ℓ)
  apply Nat.le_of_not_gt
  intro hlt
  have hUpper : Nat.card ↥(torsion ℓ E) < ℓ * ℓ := calc
    Nat.card ↥(torsion ℓ E) = Nat.card ↥(S.graphLine ℓ) * Nat.card ↥(S.resid ℓ).range :=
      S.card_torsion_eq ℓ
    _ ≤ ℓ * Nat.card ↥(S.resid ℓ).range := Nat.mul_le_mul_right _ (S.card_graphLine_le ℓ)
    _ < ℓ * ℓ := (Nat.mul_lt_mul_left (NeZero.pos ℓ)).2 hlt
  exact (Nat.not_lt_of_ge hcard) hUpper

/-- If the ℓ-torsion has `ℓ²` elements, `q` has an ℓ-th root modulo `q^{ℓℤ}`. -/
lemma exists_root_class (hcard : ℓ * ℓ ≤ Nat.card ↥(torsion ℓ E)) :
    ∃ u : kˣ, ∃ m : ℤ, u ^ ℓ = S.t.q ^ (1 + (ℓ : ℤ) * m) := by
  have hOne : (1 : ZMod ℓ) ∈ (S.resid ℓ).range := by
    rw [S.resid_range_eq_top ℓ hcard]
    trivial
  obtain ⟨P, hP⟩ := hOne
  rw [resid_apply, ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at hP
  obtain ⟨m, hm⟩ := hP
  refine ⟨S.rep ℓ P, m, ?_⟩
  rw [S.rep_pow, ← hm, add_comm 1 (S.expo ℓ P - 1), sub_add_cancel]

end

end AbcAdaptation.Reference.Iut.TateStructure

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/SL2Image.lean (valuation comparison)
-/

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The norm of the Tate curve's `j`-invariant is the inverse norm of its parameter. -/
theorem norm_tateJ (t : TateParameter K) (h12 : (12 : K) ≠ 0) :
    ‖t.tateJ‖ = ‖(t.q : K)‖⁻¹ := by
  rw [tateJ, norm_div, norm_pow, t.norm_tateCurve_c₄, one_pow, t.norm_tateCurve_Δ h12,
    one_div]

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TateCurvesTheta WithZero
open scoped WithZero Valued

variable {k : Type*} [Field k] [NumberField k] {w : FinitePlace k}

private theorem valued_eq_of_norm_eq {x y : localCompletion w} (hy : y ≠ 0)
    (hxy : ‖x‖ = ‖y‖) : Valued.v x = Valued.v y := by
  have hnorm : ‖x / y‖ = 1 := by
    rw [norm_div, hxy, div_self (norm_ne_zero_iff.mpr hy)]
  have hvalued := (norm_eq_one_iff_valued w (x / y)).mp hnorm
  have hy' : Valued.v y ≠ 0 := (Valued.v).ne_zero_iff.mpr hy
  rwa [map_div₀, div_eq_one_iff_eq hy'] at hvalued

/-- The valuation of a norm uniformizer has exponent −1. -/
private theorem valued_eq_of_isUniformizer (w : FinitePlace k) {π : localCompletion w}
    (hπ : IsUniformizer π) : Valued.v π = exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀⟩ := w.maximalIdeal.valuation_exists_uniformizer k
  let π₀' : localCompletion w := FinitePlace.embedding w.maximalIdeal π₀
  have hπ₀' : Valued.v π₀' = exp (-1 : ℤ) := by
    change Valued.v (FinitePlace.embedding w.maximalIdeal π₀) = _
    rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', hπ₀]
  have hπ₀_ne : π₀' ≠ 0 := (Valued.v).ne_zero_iff.mp (by rw [hπ₀']; exact exp_ne_zero)
  obtain ⟨m, hm⟩ := hπ.generates (Units.mk0 π₀' hπ₀_ne)
  have hv_eq : Valued.v π₀' = Valued.v (π ^ m) :=
    valued_eq_of_norm_eq (w := w) (zpow_ne_zero _ hπ.ne_zero)
      (by simpa only [Units.val_mk0, norm_zpow] using hm)
  let a : ℤ := log (Valued.v π)
  have hva : Valued.v π = exp a := (exp_log ((Valued.v).ne_zero_iff.mpr hπ.ne_zero)).symm
  have ha_neg : a < 0 := by
    have h := (norm_lt_one_iff_valued w π).mp hπ.norm_lt_one
    rwa [hva, ← exp_zero, exp_lt_exp] at h
  have hma : (-1 : ℤ) = m * a := by
    rwa [hπ₀', map_zpow₀, hva, ← exp_zsmul, exp_inj, smul_eq_mul] at hv_eq
  have hunit : IsUnit a := IsUnit.of_mul_eq_one (-m) (by
    rw [mul_neg, mul_comm a m, ← hma]
    norm_num)
  have ha : a = -1 := by
    rcases Int.isUnit_iff.mp hunit with h | h
    · omega
    · exact h
  rw [hva, ha]

/-- The valuation exponent of a Tate parameter is its negative normalized order. -/
private theorem valued_tateParameter_q (t : TateParameter (localCompletion w))
    {π : localCompletion w} (hπ : IsUniformizer π) :
    Valued.v (t.q : localCompletion w) = exp (-((t.toOrdered hπ).orderNat : ℤ)) := by
  have hnorm : ‖(t.q : localCompletion w)‖ = ‖π ^ t.orderZ hπ‖ := by
    rw [norm_zpow, t.norm_q_eq_zpow hπ]
  calc
    Valued.v (t.q : localCompletion w) = Valued.v (π ^ t.orderZ hπ) :=
      valued_eq_of_norm_eq (w := w) (zpow_ne_zero _ hπ.ne_zero) hnorm
    _ = exp (-(t.orderZ hπ)) := by
      rw [map_zpow₀, valued_eq_of_isUniformizer w hπ, ← exp_zsmul, smul_eq_mul, mul_neg_one]
    _ = _ := by
      change exp (-(t.orderZ hπ)) = exp (-((t.orderZ hπ).toNat : ℤ))
      rw [Int.toNat_of_nonneg (t.orderZ_pos hπ).le]

end AbcAdaptation.Reference.Iut

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/SL2Image.lean (lines 180–213)
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  TateCurvesTheta WeierstrassCurve WithZero
open scoped WithZero Valued

universe u

private theorem valued_finitePlaceEmbedding {k : Type*} [Field k] [NumberField k]
    {w : FinitePlace k} (x : k) :
    Valued.v (FinitePlace.embedding w.maximalIdeal x : localCompletion w) =
      w.maximalIdeal.valuation k x := by
  rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

private theorem valued_q_eq_inv_tateJ {k : Type*} [Field k] [NumberField k]
    {w : FinitePlace k} (t : TateParameter (localCompletion w)) :
    Valued.v (t.q : localCompletion w) = (Valued.v t.tateJ)⁻¹ := by
  have hnorm : ‖t.tateJ * (t.q : localCompletion w)‖ = 1 := by
    rw [norm_mul, t.norm_tateJ (twelve_ne_zero w),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr t.q.ne_zero)]
  rw [norm_eq_one_iff_valued w, map_mul] at hnorm
  rw [eq_inv_of_mul_eq_one_left hnorm, inv_inv]

namespace EllipticCurveData

/-- The Tate root identity above a multiplicative place gives divisibility of the relative
ramification index if the supplied Tate parameter order at the base place is prime to ℓ. -/
theorem prime_dvd_ramificationIdx_of_root_class (C : EllipticCurveData.{u})
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (R : C.ModEllRepData ℓ)
    {w : FinitePlace C.F} (hw : w ∈ C.badAll) (hP2 : ¬ ℓ ∣ TI.qOrder w hw)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w)
    (S : TateStructure (curveKw C.E R.torsionField w'))
    (u : (localCompletion w')ˣ) (m : ℤ) (hu : u ^ ℓ = S.t.q ^ (1 + (ℓ : ℤ) * m)) :
    ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  let e := w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal
  let n := TI.qOrder w hw
  have hqF : Valued.v ((TI.tate w hw).q : localCompletion w) = exp (-(n : ℤ)) :=
    valued_tateParameter_q _ (TI.unif_isUniformizer w hw)
  have hjF : w.maximalIdeal.valuation C.F C.E.j = exp (n : ℤ) := by
    have h := valued_q_eq_inv_tateJ (TI.tate w hw)
    rw [hqF, TI.tateJ_eq w hw, valued_finitePlaceEmbedding] at h
    rw [← inv_inv (w.maximalIdeal.valuation C.F C.E.j), ← h, ← exp_neg, neg_neg]
  have hJ : S.t.tateJ =
      FinitePlace.embedding w'.maximalIdeal (algebraMap C.F ↥R.torsionField C.E.j) := by
    calc
      S.t.tateJ = (S.C • curveKw C.E R.torsionField w').j := by
        change S.t.tateCurve.c₄ ^ 3 / S.t.tateCurve.Δ = _
        rw [← S.hC, j_eq_inv_Δ_mul, div_eq_inv_mul]
      _ = (curveKw C.E R.torsionField w').j := variableChange_j _ _
      _ = _ := by
        change ((C.E.map (algebraMap C.F ↥R.torsionField)).map
          (FinitePlace.embedding w'.maximalIdeal)).j = _
        rw [map_j, map_j]
  have hqK : Valued.v (S.t.q : localCompletion w') = exp (-((e : ℤ) * n)) := by
    rw [valued_q_eq_inv_tateJ, hJ, valued_finitePlaceEmbedding,
      Tripod.valuation_algebraMap_eq_pow hw'w, hjF, ← exp_nsmul, ← exp_neg, nsmul_eq_mul]
  have hu' := congrArg (fun x : (localCompletion w')ˣ => Valued.v (x : localCompletion w')) hu
  simp only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_pow, map_zpow₀] at hu'
  rw [hqK] at hu'
  have hu0 : Valued.v (u : localCompletion w') ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  rw [← exp_log hu0, ← exp_nsmul, ← exp_zsmul, exp_inj, nsmul_eq_mul, smul_eq_mul] at hu'
  have hdvd : (ℓ : ℤ) ∣ (1 + (ℓ : ℤ) * m) * ((e : ℤ) * n) :=
    ⟨-log (Valued.v (u : localCompletion w')), by linear_combination hu'⟩
  have hmul : (ℓ : ℤ) ∣ ((ℓ : ℤ) * m) * ((e : ℤ) * n) :=
    ⟨m * ((e : ℤ) * n), mul_assoc _ _ _⟩
  rw [add_mul, one_mul, dvd_add_left hmul] at hdvd
  have hdvd' : ℓ ∣ e * n := by exact_mod_cast hdvd
  exact (hℓ.dvd_mul.mp hdvd').resolve_right hP2

end EllipticCurveData
end AbcAdaptation.Reference.Iut

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/SL2Image.lean and Iut/Cor312/ThetaData/PointMap.lean
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

open NumberField WeierstrassCurve Anabelian
open scoped Classical Valued

universe u

noncomputable section

variable (C : EllipticCurveData.{u}) {ℓ : ℕ} (R : C.ModEllRepData ℓ)

local instance (priority := 1100) instDecidableEqTorsionFieldLocal :
    DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- Base change to the completion embeds global torsion into local torsion. -/
lemma card_torsion_curveKw_ge (w' : FinitePlace ↥R.torsionField)
    [Finite ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w'))] :
    ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w')) := by
  let f : ↥R.TK →+ ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w')) :=
    ((pointMap (curveK C.E R.torsionField) (emb R.torsionField w')).domRestrict R.TK).codRestrict _
      (fun P => by
        rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
        have hP : ℓ • P = 0 := Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp P.2)
        rw [hP, map_zero])
  have hpoint : Function.Injective
      (pointMap (curveK C.E R.torsionField) (emb R.torsionField w')) := by
    letI := (emb R.torsionField w').toAlgebra
    exact Affine.Point.map_injective (W' := curveK C.E R.torsionField)
      (S := ↥R.torsionField) (F := ↥R.torsionField) (K := localCompletion w')
      (Algebra.ofId ↥R.torsionField (localCompletion w'))
  have hf : Function.Injective f := fun P P' h => by
    apply Subtype.ext
    apply hpoint
    have h' := congrArg Subtype.val h
    simpa only [f, AddMonoidHom.codRestrict_apply, AddMonoidHom.domRestrict_apply] using h'
  calc
    ℓ * ℓ = Nat.card ↥R.TK := by rw [R.card_torsionBy_EK, sq]
    _ ≤ _ := Nat.card_le_card_of_injective f hf

/-- A Tate structure over the torsion field completion supplies the root class needed
for divisibility of the relative ramification index. -/
theorem prime_dvd_ramificationIdx_of_tateStructure (TI : C.TateInputs) (hℓ : ℓ.Prime)
    {w : FinitePlace C.F} (hw : w ∈ C.badAll) (hP2 : ¬ ℓ ∣ TI.qOrder w hw)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w)
    (S : TateStructure (curveKw C.E R.torsionField w')) :
    ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Finite ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w')) :=
    S.finite_torsion ℓ
  obtain ⟨u, m, hu⟩ := S.exists_root_class ℓ (C.card_torsion_curveKw_ge R w')
  exact C.prime_dvd_ramificationIdx_of_root_class TI hℓ R hw hP2 hw'w S u m hu

end

end AbcAdaptation.Reference.Iut.EllipticCurveData

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Existence.lean and Iut/Concrete/SL2Image.lean
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

open NumberField
open scoped Classical Valued

universe u

noncomputable section

section BadPlaces

variable (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic) {ℓ : ℕ}

include CA in
/-- The pullback of the selected bad places is the multiplicative locus away from `2` and `ℓ`. -/
lemma badPlacesOver_VBadOf :
    badPlacesOver C.F C.E (C.VBadOf ℓ) =
      {w | w ∈ C.badAll ∧ residueChar w ≠ 2 ∧ residueChar w ≠ ℓ} := by
  ext w
  constructor
  · rintro ⟨v, ⟨h2, hℓ, -, hmult⟩, hwv⟩
    refine ⟨hmult w hwv, ?_, ?_⟩ <;> rw [CA.residueChar_liesOver v w hwv] <;> assumption
  · rintro ⟨hw, h2, hℓ⟩
    obtain ⟨v, hwv⟩ := CA.exists_liesOver w
    have hres := CA.residueChar_liesOver v w hwv
    have hv2 : residueChar v ≠ 2 := by rwa [← hres]
    have hvℓ : residueChar v ≠ ℓ := by rwa [← hres]
    refine ⟨v, ⟨hv2, hvℓ, ⟨w, hwv⟩, ?_⟩, hwv⟩
    exact fun w₀ hw₀ => CA.mult_invariant v hv2 w w₀ hwv hw₀ hw

variable (R : C.ModEllRepData ℓ)

include CA in
private theorem torsionField_isBadPlace_of_liesOver
    {w : FinitePlace C.F} (hw : w ∈ C.badAll)
    (h2 : residueChar w ≠ 2) (hwℓ : residueChar w ≠ ℓ)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w) :
    IsBadPlace C.E R.torsionField (C.VBadOf ℓ) w' := by
  have hmem : w ∈ badPlacesOver C.F C.E (C.VBadOf ℓ) := by
    rw [C.badPlacesOver_VBadOf CA]
    exact ⟨hw, h2, hwℓ⟩
  obtain ⟨v, hv, hwv⟩ := hmem
  let K := R.torsionField
  letI : Algebra ↥(fieldOfModuli C.F C.E) ↥K :=
    (fieldOfModuli C.F C.E).instAlgebraSubtypeMem
  have hmap : algebraMap ↥(fieldOfModuli C.F C.E) ↥K =
      (algebraMap C.F ↥K).comp (algebraMap ↥(fieldOfModuli C.F C.E) C.F) :=
    RingHom.ext fun _ => rfl
  letI : IsScalarTower ↥(fieldOfModuli C.F C.E) C.F ↥K :=
    IsScalarTower.of_algebraMap_eq' hmap
  letI : IsScalarTower (𝓞 ↥(fieldOfModuli C.F C.E)) (𝓞 C.F) (𝓞 ↥K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hmap x)
  haveI : w'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hw'w
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact ⟨v, hv, ⟨(Ideal.LiesOver.trans w'.maximalIdeal.asIdeal
    w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal).over⟩⟩

end BadPlaces

end

end AbcAdaptation.Reference.Iut.EllipticCurveData

open AbcAdaptation.Reference.Iut NumberField
open scoped Classical Valued

universe u

theorem solution (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (R : C.ModEllRepData ℓ)
    {w : FinitePlace C.F} (hw : w ∈ C.badAll)
    (h2 : residueChar w ≠ 2) (hwℓ : residueChar w ≠ ℓ) (hP2 : ¬ ℓ ∣ TI.qOrder w hw)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w) :
    ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  have hbad := EllipticCurveData.torsionField_isBadPlace_of_liesOver C CA R hw h2 hwℓ hw'w
  let TK := AddSubgroup.torsionBy (curveK C.E R.torsionField).toAffine.Point ℓ
  have hcard : ℓ * ℓ ≤ Nat.card ↥TK := by
    let torsionCard (decEq : DecidableEq ↥R.torsionField) : ℕ :=
      letI := decEq
      Nat.card ↥(AddSubgroup.torsionBy (curveK C.E R.torsionField).toAffine.Point ℓ)
    change ℓ * ℓ ≤ torsionCard inferInstance
    have hcardLocal : ℓ * ℓ ≤ torsionCard (fun a b => Classical.propDecidable (a = b)) := by
      change ℓ * ℓ ≤ Nat.card ↥R.TK
      rw [R.card_torsionBy_EK, sq]
    exact (congrArg torsionCard (Subsingleton.elim _ _)) ▸ hcardLocal
  obtain ⟨S⟩ := nonempty_tateStructure_of_torsion C.E R.torsionField (VBad := C.VBadOf ℓ)
    (fun _ hv => hv.1) (fun _ hv w₀ hwv₀ => hv.2.2.2 w₀ hwv₀) hℓ hodd TK le_rfl hcard hbad
  exact C.prime_dvd_ramificationIdx_of_tateStructure R TI hℓ hw hP2 hw'w S


#print axioms solution

namespace TateStructureSketchAudit

open Lean

/- Check that the sole Open child supplies the sketch's only use of `sorryAx`. -/
run_meta do
  let env ← getEnv
  let child := `AbcAdaptation.Reference.Iut.nonempty_tateStructure_of_torsion
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let childAxioms ← collectAxioms child
  unless childAxioms.contains `sorryAx do
    throwError "Expected an Open platform child"
  for ax in childAxioms do
    unless ax == `sorryAx || allowed.contains ax do
      throwError "Unexpected axiom in platform child: {ax}"
  let mut seen : NameSet := {}
  let mut pending := [`solution]
  while let name :: rest := pending do
    pending := rest
    if !seen.contains name then
      seen := seen.insert name
      let ci ← getConstInfo name
      if name == child then
        pending := ci.type.getUsedConstants.toList ++ pending
      else if (env.getModuleIdxFor? name).isSome then
        for ax in ← collectAxioms name do
          unless allowed.contains ax do
            throwError "Unexpected axiom outside the platform child proof in {name}: {ax}"
      else
        if let .axiomInfo _ := ci then
          unless allowed.contains name do
            throwError "Unexpected axiom declared in the sketch: {name}"
        let values := (ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
        let constructors := match ci with
          | .inductInfo info => info.ctors.toArray
          | _ => #[]
        pending := (ci.type.getUsedConstants ++ values ++ constructors).toList ++ pending
  unless seen.contains child do
    throwError "The sketch does not use the Open platform child"
  logInfo "The declared platform child is the only source of sorryAx in the sketch."

end TateStructureSketchAudit
