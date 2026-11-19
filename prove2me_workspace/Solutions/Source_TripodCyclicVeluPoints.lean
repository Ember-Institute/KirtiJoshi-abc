/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/CyclicPoints.lean (Legendre points and halves)
               and Iut/Tripod/CyclicIsogeny.lean (the designated pairs)
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCyclicVeluRatio
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.TateFamily
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Solutions.Source_ModEllRepGalois
import Solutions.Source_TripodUnramifiedBase
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace AbcAdaptation.Tripod.CyclicPoints

open WeierstrassCurve WeierstrassCurve.Affine
open JoshiTeich.Act1Scene1.IutCyclicVelu (xCoordinate)

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {l : F}
variable (hW : W = legendre l)
include hW

private lemma equation_iff {x y : F} :
    W.toAffine.Equation x y ↔ y ^ 2 = x * (x - 1) * (x - l) := by
  subst W
  rw [Affine.equation_iff]
  simp only [legendre_a₁, legendre_a₂, legendre_a₃, legendre_a₄, legendre_a₆]
  constructor <;> intro h <;> linear_combination h

private lemma negY_eq (x y : F) : W.toAffine.negY x y = -y := by
  subst W
  exact legendre_negY l x y

/-- The point `(0, 0)` on the Legendre model. -/
def pt₁ : W.toAffine.Point :=
  Point.mk (x := 0) (y := 0) ((equation_iff hW).mpr (by ring))

/-- The point `(1, 0)` on the Legendre model. -/
def pt₂ : W.toAffine.Point :=
  Point.mk (x := 1) (y := 0) ((equation_iff hW).mpr (by ring))

/-- The half of `(0, 0)` with coordinates `(s, i * s * (s - 1))`. -/
def half₁ {s i : F} (hs : s ^ 2 = l) (hi : i ^ 2 = -1) : W.toAffine.Point :=
  Point.mk (x := s) (y := i * s * (s - 1)) ((equation_iff hW).mpr (by
    rw [← hs]
    linear_combination (s ^ 2 * (s - 1) ^ 2) * hi))

/-- The half of `(1, 0)` with coordinates `(1 + s, s * (1 + s))`. -/
def half₂ {s : F} (hs : s ^ 2 = 1 - l) : W.toAffine.Point :=
  Point.mk (x := 1 + s) (y := s * (1 + s)) ((equation_iff hW).mpr (by
    have hl : l = 1 - s ^ 2 := by rw [hs]; ring
    rw [hl]
    ring))

@[simp] lemma xCoordinate_pt₁ : xCoordinate (pt₁ hW) = 0 := rfl
@[simp] lemma xCoordinate_pt₂ : xCoordinate (pt₂ hW) = 1 := rfl
@[simp] lemma xCoordinate_half₁ {s i : F} (hs : s ^ 2 = l) (hi : i ^ 2 = -1) :
    xCoordinate (half₁ hW hs hi) = s := rfl
@[simp] lemma xCoordinate_half₂ {s : F} (hs : s ^ 2 = 1 - l) :
    xCoordinate (half₂ hW hs) = 1 + s := rfl

lemma pt₁_ne_zero : pt₁ hW ≠ 0 := Point.some_ne_zero _
lemma pt₂_ne_zero : pt₂ hW ≠ 0 := Point.some_ne_zero _

variable [DecidableEq F]

lemma pt₁_add_self : pt₁ hW + pt₁ hW = 0 :=
  Point.add_self_of_Y_eq (by rw [negY_eq hW, neg_zero])

lemma pt₂_add_self : pt₂ hW + pt₂ hW = 0 :=
  Point.add_self_of_Y_eq (by rw [negY_eq hW, neg_zero])

variable [NeZero (2 : F)]

/-- Doubling the designated first half gives the point `(0, 0)`. -/
lemma half₁_add_self (hl0 : l ≠ 0) (hl1 : l ≠ 1) {s i : F} (hs : s ^ 2 = l)
    (hi : i ^ 2 = -1) : half₁ hW hs hi + half₁ hW hs hi = pt₁ hW := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hl0
    rw [← hs]
    ring
  have hs1 : s - 1 ≠ 0 := by
    intro h
    apply hl1
    rw [← hs, sub_eq_zero.mp h]
    ring
  have hi0 : i ≠ 0 := by rintro rfl; norm_num at hi
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have hy : i * s * (s - 1) ≠ W.toAffine.negY s (i * s * (s - 1)) := by
    rw [negY_eq hW]
    intro h
    have : 2 * (i * s * (s - 1)) = 0 := by linear_combination h
    simp [h2, hi0, hs0, hs1] at this
  have ha₁ : W.a₁ = 0 := by subst W; rfl
  have ha₂ : W.a₂ = -(1 + l) := by subst W; rfl
  have ha₄ : W.a₄ = l := by subst W; rfl
  have hslope : W.toAffine.slope s s (i * s * (s - 1)) (i * s * (s - 1)) = i * (s - 1) := by
    rw [slope_of_Y_ne rfl hy, div_eq_iff (sub_ne_zero.mpr hy), negY_eq hW, ha₁, ha₂, ha₄, ← hs]
    linear_combination (-(2 * s * (s - 1) ^ 2)) * hi
  have hX : W.toAffine.addX s s (i * (s - 1)) = 0 := by
    rw [addX, ha₁, ha₂, ← hs]
    linear_combination (s - 1) ^ 2 * hi
  unfold half₁ pt₁ Point.mk
  rw [Point.add_self_of_Y_ne hy, Point.some.injEq, hslope]
  refine ⟨hX, ?_⟩
  rw [addY, negAddY, hX, negY_eq hW]
  ring

/-- Doubling the designated second half gives the point `(1, 0)`. -/
lemma half₂_add_self (hl0 : l ≠ 0) (hl1 : l ≠ 1) {s : F} (hs : s ^ 2 = 1 - l) :
    half₂ hW hs + half₂ hW hs = pt₂ hW := by
  have hs0 : s ≠ 0 := by rintro rfl; apply hl1; linear_combination hs
  have hs1 : 1 + s ≠ 0 := by
    intro h
    apply hl0
    have : s = -1 := by linear_combination h
    rw [this] at hs
    linear_combination hs
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have hy : s * (1 + s) ≠ W.toAffine.negY (1 + s) (s * (1 + s)) := by
    rw [negY_eq hW]
    intro h
    have : 2 * (s * (1 + s)) = 0 := by linear_combination h
    simp [h2, hs0, hs1] at this
  have ha₁ : W.a₁ = 0 := by subst W; rfl
  have ha₂ : W.a₂ = -(1 + l) := by subst W; rfl
  have ha₄ : W.a₄ = l := by subst W; rfl
  have hl : l = 1 - s ^ 2 := by rw [hs]; ring
  have hslope : W.toAffine.slope (1 + s) (1 + s) (s * (1 + s)) (s * (1 + s)) = 1 + s := by
    rw [slope_of_Y_ne rfl hy, div_eq_iff (sub_ne_zero.mpr hy), negY_eq hW, ha₁, ha₂, ha₄, hl]
    ring
  have hX : W.toAffine.addX (1 + s) (1 + s) (1 + s) = 1 := by
    rw [addX, ha₁, ha₂, hl]
    ring
  unfold half₂ pt₂ Point.mk
  rw [Point.add_self_of_Y_ne hy, Point.some.injEq, hslope]
  refine ⟨hX, ?_⟩
  rw [addY, negAddY, hX, negY_eq hW]
  ring

end AbcAdaptation.Tripod.CyclicPoints

namespace AbcAdaptation.Tripod.Cyclic

open AbcAdaptation.Reference.Iut WeierstrassCurve CyclicPoints
open JoshiTeich.Act1Scene1.IutCyclicVelu (xCoordinate xCoordinate_zero)
open scoped Classical

attribute [local instance 1100] JoshiTeich.ReferenceIut.instDecidableEqIntermediateField

variable (P : CurveProviders) (x : Pt)

lemma genC'_ne_zero : genC' P x ≠ 0 := gen'_ne_zero x.2.1
lemma genC'_ne_one : genC' P x ≠ 1 := gen'_ne_one x.2.2

/-- The first designated two-torsion point over the base field. -/
def T₁Base : (Affine.baseChange (P.curve x).E (P.curve x).F).Point :=
  pt₁ (W := (P.curve x).E) (curve_E_eq P x)

/-- The second designated two-torsion point over the base field. -/
def T₂Base : (Affine.baseChange (P.curve x).E (P.curve x).F).Point :=
  pt₂ (W := (P.curve x).E) (curve_E_eq P x)

/-- The first designated half over the base field. -/
def R₁Base : (Affine.baseChange (P.curve x).E (P.curve x).F).Point :=
  half₁ (W := (P.curve x).E) (curve_E_eq P x) (sqrtLam'_sq P x) (sqrtNegOne'_sq P x)

/-- The second designated half over the base field. -/
def R₂Base : (Affine.baseChange (P.curve x).E (P.curve x).F).Point :=
  half₂ (W := (P.curve x).E) (curve_E_eq P x) (sqrtOneSubLam'_sq P x)

lemma T₁Base_ne_zero : T₁Base P x ≠ 0 :=
  pt₁_ne_zero (W := (P.curve x).E) (curve_E_eq P x)
lemma T₂Base_ne_zero : T₂Base P x ≠ 0 :=
  pt₂_ne_zero (W := (P.curve x).E) (curve_E_eq P x)
lemma T₁Base_add_self : T₁Base P x + T₁Base P x = 0 :=
  pt₁_add_self (W := (P.curve x).E) (curve_E_eq P x)
lemma T₂Base_add_self : T₂Base P x + T₂Base P x = 0 :=
  pt₂_add_self (W := (P.curve x).E) (curve_E_eq P x)
lemma R₁Base_add_self : R₁Base P x + R₁Base P x = T₁Base P x :=
  half₁_add_self (W := (P.curve x).E) (curve_E_eq P x) (genC'_ne_zero P x) (genC'_ne_one P x)
    (sqrtLam'_sq P x) (sqrtNegOne'_sq P x)
lemma R₂Base_add_self : R₂Base P x + R₂Base P x = T₂Base P x :=
  half₂_add_self (W := (P.curve x).E) (curve_E_eq P x) (genC'_ne_zero P x) (genC'_ne_one P x)
    (sqrtOneSubLam'_sq P x)

variable {ℓ : ℕ} (hℓ : ℓ.Prime)

/-- The `ℓ`-torsion field of the provider's curve. -/
abbrev L : IntermediateField (P.curve x).F (P.curve x).Fbar :=
  (P.modRep x ℓ hℓ).torsionField

/-- The provider's curve over the `ℓ`-torsion field. -/
abbrev WL : WeierstrassCurve (L P x hℓ) := (P.modRep x ℓ hℓ).EK

/-- The Legendre parameter in the `ℓ`-torsion field. -/
abbrev lamL : L P x hℓ :=
  algebraMap (P.curve x).F (L P x hℓ) (genC' P x)

lemma WL_eq : WL P x hℓ = legendre (lamL P x hℓ) := by
  change Affine.baseChange (P.curve x).E (L P x hℓ) = _
  exact (congrArg (fun W : WeierstrassCurve (P.curve x).F =>
    Affine.baseChange W (L P x hℓ)) (curve_E_eq P x)).trans
      (legendre_baseChange (genC' P x))

/-- Base change from the provider's original field to its `ℓ`-torsion field. -/
abbrev baseChangeToL : (Affine.baseChange (P.curve x).E (P.curve x).F).Point →+
    (WL P x hℓ).toAffine.Point :=
  Affine.Point.baseChange (W' := (P.curve x).E) (P.curve x).F (L P x hℓ)

private lemma baseChangeToL_injective : Function.Injective (baseChangeToL P x hℓ) :=
  Affine.Point.map_injective (W' := (P.curve x).E) (Algebra.ofId (P.curve x).F (L P x hℓ))

/-- Composition with the inclusion into the algebraic closure gives direct base change. -/
lemma bcK_baseChangeToL (Q : (Affine.baseChange (P.curve x).E (P.curve x).F).Point) :
    (P.modRep x ℓ hℓ).bcK (baseChangeToL P x hℓ Q) =
      Affine.Point.baseChange (W' := (P.curve x).E) (P.curve x).F (P.curve x).Fbar Q :=
  Affine.Point.map_baseChange (W' := (P.curve x).E)
    (IsScalarTower.toAlgHom (P.curve x).F (L P x hℓ) (P.curve x).Fbar) Q

/-- The point `(0, 0)` over the torsion field. -/
def T₁ : (WL P x hℓ).toAffine.Point := baseChangeToL P x hℓ (T₁Base P x)

/-- The point `(1, 0)` over the torsion field. -/
def T₂ : (WL P x hℓ).toAffine.Point := baseChangeToL P x hℓ (T₂Base P x)

/-- The first designated half over the torsion field. -/
def R₁ : (WL P x hℓ).toAffine.Point := baseChangeToL P x hℓ (R₁Base P x)

/-- The second designated half over the torsion field. -/
def R₂ : (WL P x hℓ).toAffine.Point := baseChangeToL P x hℓ (R₂Base P x)

lemma T₁_ne_zero : T₁ P x hℓ ≠ 0 := fun h =>
  T₁Base_ne_zero P x (baseChangeToL_injective P x hℓ
    (h.trans (map_zero (baseChangeToL P x hℓ)).symm))

lemma T₂_ne_zero : T₂ P x hℓ ≠ 0 := fun h =>
  T₂Base_ne_zero P x (baseChangeToL_injective P x hℓ
    (h.trans (map_zero (baseChangeToL P x hℓ)).symm))

lemma T₁_add_self : T₁ P x hℓ + T₁ P x hℓ = 0 := by
  rw [T₁, ← map_add, T₁Base_add_self, map_zero]

lemma T₂_add_self : T₂ P x hℓ + T₂ P x hℓ = 0 := by
  rw [T₂, ← map_add, T₂Base_add_self, map_zero]

lemma R₁_add_self : R₁ P x hℓ + R₁ P x hℓ = T₁ P x hℓ := by
  rw [R₁, T₁, ← map_add, R₁Base_add_self]

lemma R₂_add_self : R₂ P x hℓ + R₂ P x hℓ = T₂ P x hℓ := by
  rw [R₂, T₂, ← map_add, R₂Base_add_self]

lemma T₁_ne_T₂ : T₁ P x hℓ ≠ T₂ P x hℓ := by
  intro h
  have hbase := baseChangeToL_injective P x hℓ h
  have hx := congrArg (fun Q : (P.curve x).E.toAffine.Point => xCoordinate Q) hbase
  have h01 : (0 : (P.curve x).F) = 1 := by
    simpa only [T₁Base, T₂Base, xCoordinate_pt₁, xCoordinate_pt₂] using hx
  exact zero_ne_one h01

private lemma xCoordinate_baseChangeToL
    (Q : (Affine.baseChange (P.curve x).E (P.curve x).F).Point) :
    xCoordinate (baseChangeToL P x hℓ Q) =
      algebraMap (P.curve x).F (L P x hℓ) (xCoordinate Q) := by
  cases Q with
  | zero =>
    change xCoordinate (baseChangeToL P x hℓ 0) = algebraMap (P.curve x).F (L P x hℓ) 0
    simp only [map_zero, xCoordinate_zero]
  | some a b h => rfl

lemma xCoordinate_T₁_sub_R₁ :
    xCoordinate (T₁ P x hℓ) - xCoordinate (R₁ P x hℓ) =
      -algebraMap (P.curve x).F (L P x hℓ) (sqrtLam' P x) := by
  change xCoordinate (baseChangeToL P x hℓ (T₁Base P x)) -
    xCoordinate (baseChangeToL P x hℓ (R₁Base P x)) = _
  rw [xCoordinate_baseChangeToL, xCoordinate_baseChangeToL]
  change algebraMap (P.curve x).F (L P x hℓ) 0 -
    algebraMap (P.curve x).F (L P x hℓ) (sqrtLam' P x) = _
  rw [map_zero, zero_sub]

lemma xCoordinate_T₂_sub_R₂ :
    xCoordinate (T₂ P x hℓ) - xCoordinate (R₂ P x hℓ) =
      -algebraMap (P.curve x).F (L P x hℓ) (sqrtOneSubLam' P x) := by
  change xCoordinate (baseChangeToL P x hℓ (T₂Base P x)) -
    xCoordinate (baseChangeToL P x hℓ (R₂Base P x)) = _
  rw [xCoordinate_baseChangeToL, xCoordinate_baseChangeToL]
  change algebraMap (P.curve x).F (L P x hℓ) 1 -
    algebraMap (P.curve x).F (L P x hℓ) (1 + sqrtOneSubLam' P x) = _
  rw [map_add, map_one]
  ring

end AbcAdaptation.Tripod.Cyclic
