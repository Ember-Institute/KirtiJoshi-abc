import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily
import Definitions.Def_AbcAdaptation_Tripod_PlaceUnder
import Definitions.Def_AbcAdaptation_Tripod_RelativeValuation
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Theorems.Thm_AbcAdaptation_Reference_Iut_exists_tateUniformization

set_option autoImplicit false

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original paths Iut/Cor312/ThetaData/Places.lean and BadPlaceNorm.lean,
Iut/Concrete/ThetaLocalConstruct/Ordp.lean and Iut/Tripod/Height.lean
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
-/
namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

section
variable {k : Type*} [Field k] [NumberField k]
lemma residueChar_prime (w : FinitePlace k) : (residueChar w).Prime := by
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ w.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 k ⧸ w.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.maximalIdeal.ne_bot
  exact CharP.char_is_prime (𝓞 k ⧸ w.maximalIdeal.asIdeal) (ringChar _)
end

section
variable {K : Type*} [Field K] [NumberField K]
lemma under_int_eq (v : FinitePlace K) :
    v.maximalIdeal.asIdeal.under ℤ = Ideal.span {(residueChar v : ℤ)} := by
  set P := v.maximalIdeal.asIdeal
  have hp : (residueChar v).Prime := residueChar_prime v
  haveI : CharP (𝓞 K ⧸ P) (residueChar v) := ringChar.charP _
  have hmem : (residueChar v : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.natCast_mem_of_charP_quotient (residueChar v) P
  have hle : Ideal.span {(residueChar v : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  haveI hprime : (Ideal.span {(residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have hmax : (Ideal.span {(residueChar v : ℤ)}).IsMaximal :=
    IsPrime.to_maximal_ideal (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero)
  haveI : (P.under ℤ).IsPrime := Ideal.comap_isPrime _ _
  exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm

end

section
variable {k : Type*} [Field k] [NumberField k]
lemma two_mem_maximalIdeal_iff (v : FinitePlace k) :
    (2 : 𝓞 k) ∈ v.maximalIdeal.asIdeal ↔ residueChar v = 2 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h2 : (Ideal.Quotient.mk v.maximalIdeal.asIdeal (2 : 𝓞 k)) =
      ((2 : ℕ) : 𝓞 k ⧸ v.maximalIdeal.asIdeal) := by
    rw [map_ofNat, Nat.cast_ofNat]
  rw [h2, CharP.cast_eq_zero_iff (𝓞 k ⧸ v.maximalIdeal.asIdeal) (ringChar _)]
  exact Nat.prime_dvd_prime_iff_eq (residueChar_prime v) Nat.prime_two
end

section
variable {T : Type*} [Field T] [NumberField T]
lemma valuation_two_eq_one_of_ne {w : FinitePlace T} (h2 : residueChar w ≠ 2) :
    w.maximalIdeal.valuation T 2 = 1 := by
  have : (2 : T) = algebraMap (𝓞 T) T 2 := by rw [map_ofNat]
  rw [this, valuation_eq_one_iff_notMem, two_mem_maximalIdeal_iff]
  exact h2

end

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

section Tower
variable {v : FinitePlace K} {w : FinitePlace k} (hvw : FinitePlace.LiesOver v w)
include hvw

/-- The prime of `ℤ` below `v` is the prime below `w`. -/
lemma under_int_eq_under_int : v.maximalIdeal.asIdeal.under ℤ = w.maximalIdeal.asIdeal.under ℤ := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  rw [← Ideal.under_under (B := 𝓞 k) v.maximalIdeal.asIdeal,
    ← Ideal.over_def v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal]

/-- Places over each other have the same residue characteristic. -/
lemma residueChar_eq_of_liesOver : residueChar v = residueChar w := by
  have h := under_int_eq_under_int hvw
  rw [under_int_eq, under_int_eq, Ideal.span_singleton_eq_span_singleton] at h
  have h' := Int.natAbs_eq_iff_associated.mpr h
  simpa using h'

end Tower

end AbcAdaptation.Tripod

/-
Adapted from Iut/Cor312/ThetaData/VariableChangePoint.lean.
Source snapshot 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8, lana-agents/iut.
Upstream commit a0879d37aa370169cbdd563d2919b02318166541, Git author Christian Merten.
The imports and namespace are adapted for Prove2Me.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# Points of Weierstrass curves along changes of variables

A change of variables `C = (u, r, s, t)` (Mathlib's `WeierstrassCurve.VariableChange`, with the
convention `X = u²X' + r`, `Y = u³Y' + u²sX' + t`) identifies the points of `W` with those of
`C • W`: the point `(x, y)` of `W` corresponds to the point
`(X', Y') = ((x - r)/u², (y - t - s(x - r))/u³)` of `C • W`. This identification respects the
group law (the addition formulas are equivariant under the affine substitution, the slope of a
line transforming as `ℓ ↦ (ℓ - s)/u`). We record it as the additive isomorphism
`AbcAdaptation.Reference.Iut.Anabelian.vcEquiv C W : W(k) ≃+ (C • W)(k)`.
-/

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve
open scoped Classical

noncomputable section

section Coordinates

variable {k : Type*} [Field k] (C : VariableChange k) (W : WeierstrassCurve k)

/-- The `X`-coordinate in the model `C • W` of a point with `x`-coordinate `x`. -/
def vcX (x : k) : k := (x - C.r) / (C.u : k) ^ 2

/-- The `Y`-coordinate in the model `C • W` of the point `(x, y)`. -/
def vcY (x y : k) : k := (y - C.t - C.s * (x - C.r)) / (C.u : k) ^ 3

lemma u_ne_zero : (C.u : k) ≠ 0 := C.u.ne_zero

lemma vcX_injective : Function.Injective (vcX C) := by
  intro a b h
  unfold vcX at h
  rw [div_left_inj' (pow_ne_zero _ (u_ne_zero C))] at h
  linear_combination h

lemma vcY_inj (x y y' : k) : vcY C x y = vcY C x y' ↔ y = y' := by
  unfold vcY
  rw [div_left_inj' (pow_ne_zero _ (u_ne_zero C))]
  constructor
  · intro h
    linear_combination h
  · intro h
    rw [h]

/-- `x = u²X' + r` recovers `x` from `X'`. -/
lemma vcX_of (x' : k) : vcX C ((C.u : k) ^ 2 * x' + C.r) = x' := by
  unfold vcX
  field_simp
  ring

/-- `y = u³Y' + u²sX' + t` recovers `y` from `(X', Y')`. -/
lemma vcY_of (x' y' : k) :
    vcY C ((C.u : k) ^ 2 * x' + C.r) ((C.u : k) ^ 3 * y' + (C.u : k) ^ 2 * C.s * x' + C.t) = y' := by
  unfold vcY
  field_simp
  ring

/-- The coefficients of `C • W`, in terms of the inverse of the unit `u`. -/
lemma variableChange_coeffs :
    (C • W).a₁ = (C.u : k)⁻¹ * (W.a₁ + 2 * C.s) ∧
    (C • W).a₂ = (C.u : k)⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) ∧
    (C • W).a₃ = (C.u : k)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) ∧
    (C • W).a₄ = (C.u : k)⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁
      + 3 * C.r ^ 2 - 2 * C.s * C.t) ∧
    (C • W).a₆ = (C.u : k)⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
      - C.t ^ 2 - C.r * C.t * W.a₁) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, Units.val_inv_eq_inv_val]

/-- The Weierstrass polynomial of `C • W` at the transformed point. -/
lemma evalEval_polynomial_vc (x y : k) :
    (C • W).toAffine.polynomial.evalEval (vcX C x) (vcY C x y) =
      (C.u : k)⁻¹ ^ 6 * W.toAffine.polynomial.evalEval x y := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  rw [Affine.evalEval_polynomial, Affine.evalEval_polynomial, h₁, h₂, h₃, h₄, h₆]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- The equation of `W` at `(x, y)` is the equation of `C • W` at the transformed point. -/
lemma equation_vc (x y : k) :
    W.toAffine.Equation x y ↔ (C • W).toAffine.Equation (vcX C x) (vcY C x y) := by
  rw [Affine.Equation, Affine.Equation, evalEval_polynomial_vc, mul_eq_zero, or_iff_right]
  exact pow_ne_zero _ (inv_ne_zero (u_ne_zero C))

/-- The partial derivative in `X` transforms as `∂_X' = u⁻⁴(∂_x + s ∂_y)`. -/
lemma polynomialX_vc (x y : k) :
    (C • W).toAffine.polynomialX.evalEval (vcX C x) (vcY C x y) =
      (C.u : k)⁻¹ ^ 4 * (W.toAffine.polynomialX.evalEval x y
        + C.s * W.toAffine.polynomialY.evalEval x y) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  rw [Affine.evalEval_polynomialX, Affine.evalEval_polynomialX, Affine.evalEval_polynomialY,
    h₁, h₂, h₄]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- The partial derivative in `Y` transforms as `∂_Y' = u⁻³ ∂_y`. -/
lemma polynomialY_vc (x y : k) :
    (C • W).toAffine.polynomialY.evalEval (vcX C x) (vcY C x y) =
      (C.u : k)⁻¹ ^ 3 * W.toAffine.polynomialY.evalEval x y := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  rw [Affine.evalEval_polynomialY, Affine.evalEval_polynomialY, h₁, h₃]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- Nonsingularity of `W` at `(x, y)` is nonsingularity of `C • W` at the transformed point. -/
lemma nonsingular_vc (x y : k) :
    W.toAffine.Nonsingular x y ↔ (C • W).toAffine.Nonsingular (vcX C x) (vcY C x y) := by
  rw [Affine.Nonsingular, Affine.Nonsingular, ← equation_vc, polynomialX_vc, polynomialY_vc]
  have hu4 : (C.u : k)⁻¹ ^ 4 ≠ 0 := pow_ne_zero _ (inv_ne_zero (u_ne_zero C))
  have hu3 : (C.u : k)⁻¹ ^ 3 ≠ 0 := pow_ne_zero _ (inv_ne_zero (u_ne_zero C))
  simp only [ne_eq, mul_eq_zero, hu4, hu3, false_or]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro (h | h)
    · by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact h (by linear_combination hc.1 - C.s * hc.2)
    · exact Or.inr h
  · rintro (h | h)
    · by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact h (by linear_combination hc.1 + C.s * hc.2)
    · exact Or.inr h

/-- Negation commutes with the transformation of coordinates. -/
lemma vcY_negY (x y : k) :
    vcY C x (W.toAffine.negY x y) = (C • W).toAffine.negY (vcX C x) (vcY C x y) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  unfold Affine.negY
  rw [h₁, h₃]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- The `X`-coordinate of a sum transforms compatibly, the slope transforming as
`ℓ ↦ (ℓ - s)/u`. -/
lemma vcX_addX (x₁ x₂ ℓ : k) :
    vcX C (W.toAffine.addX x₁ x₂ ℓ) =
      (C • W).toAffine.addX (vcX C x₁) (vcX C x₂) ((ℓ - C.s) / (C.u : k)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  unfold Affine.addX
  rw [h₁, h₂]
  unfold vcX
  have hu := u_ne_zero C
  field_simp
  ring

/-- The `Y`-coordinate of a sum transforms compatibly. -/
lemma vcY_addY (x₁ x₂ y₁ ℓ : k) :
    vcY C (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) =
      (C • W).toAffine.addY (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) ((ℓ - C.s) / (C.u : k)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  unfold Affine.addY Affine.negAddY Affine.negY Affine.addX
  rw [h₁, h₂, h₃]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- The slope of the line through two points transforms as `ℓ ↦ (ℓ - s)/u`. -/
lemma slope_vc {x₁ x₂ y₁ y₂ : k} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) / (C.u : k) := by
  obtain ⟨h₁', h₂', h₃', h₄', h₆'⟩ := variableChange_coeffs C W
  have hu := u_ne_zero C
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hd : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := by
      rw [sub_ne_zero]
      rcases Affine.Y_eq_of_X_eq h₁ h₂ rfl with h | h
      · rw [← h] at hy
        exact hy
      · exact absurd h hy
    have hy' : vcY C x₁ y₁ ≠ (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₂) := by
      rw [← vcY_negY, Ne, vcY_inj]
      exact hy
    rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', ← vcY_negY]
    have hN' : 3 * vcX C x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * vcX C x₁ + (C • W).toAffine.a₄
        - (C • W).toAffine.a₁ * vcY C x₁ y₁ =
        (C.u : k)⁻¹ ^ 4 * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄
          - W.toAffine.a₁ * y₁) - C.s * (y₁ - W.toAffine.negY x₁ y₁)) := by
      rw [h₁', h₂', h₄']
      unfold vcX vcY Affine.negY
      field_simp
      ring
    have hD' : vcY C x₁ y₁ - vcY C x₁ (W.toAffine.negY x₁ y₁) =
        (C.u : k)⁻¹ ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by
      unfold vcY
      field_simp
      ring
    rw [hN', hD']
    generalize y₁ - W.toAffine.negY x₁ y₁ = D at hd ⊢
    field_simp
  · have hx' : vcX C x₁ ≠ vcX C x₂ := fun h => hx (vcX_injective C h)
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx']
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hnum : vcY C x₁ y₁ - vcY C x₂ y₂ =
        (C.u : k)⁻¹ ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
      unfold vcY
      field_simp
      ring
    have hden : vcX C x₁ - vcX C x₂ = (C.u : k)⁻¹ ^ 2 * (x₁ - x₂) := by
      unfold vcX
      field_simp
      ring
    rw [hnum, hden]
    generalize x₁ - x₂ = D at hd ⊢
    field_simp

end Coordinates

/-! ## The isomorphism on points -/

section Points

variable {k : Type*} [Field k] (C : VariableChange k) (W : WeierstrassCurve k)

/-- The point of `C • W` corresponding to a point of `W`. -/
def vcPoint : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (vcX C x) (vcY C x y) ((nonsingular_vc C W x y).mp h)

/-- Two affine points with the same coordinates are equal. -/
lemma some_ext {W : WeierstrassCurve k} {x y x' y' : k} {h : W.toAffine.Nonsingular x y}
    {h' : W.toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  subst hx hy
  rfl

@[simp] lemma vcPoint_zero : vcPoint C W 0 = 0 := rfl

lemma vcPoint_some {x y : k} (h : W.toAffine.Nonsingular x y) :
    vcPoint C W (.some x y h) = .some (vcX C x) (vcY C x y) ((nonsingular_vc C W x y).mp h) := rfl

lemma vcPoint_neg (P : W.toAffine.Point) : vcPoint C W (-P) = -vcPoint C W P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some, vcPoint_some, vcPoint_some, Affine.Point.neg_some]
    exact some_ext rfl (vcY_negY C W x y)

lemma vcPoint_add (P Q : W.toAffine.Point) :
    vcPoint C W (P + Q) = vcPoint C W P + vcPoint C W Q := by
  cases P with
  | zero =>
    change vcPoint C W (0 + Q) = 0 + vcPoint C W Q
    rw [zero_add, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change vcPoint C W (_ + 0) = _ + 0
      rw [add_zero, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, vcPoint_some, vcPoint_some,
          Affine.Point.add_of_Y_eq (congrArg (vcX C) hxy.1)]
        · rfl
        · rw [hxy.2, hxy.1, vcY_negY]
      · have hxy' : ¬(vcX C x₁ = vcX C x₂ ∧
            vcY C x₁ y₁ = (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂)) := by
          rintro ⟨hx, hy⟩
          have hx' := vcX_injective C hx
          subst hx'
          rw [← vcY_negY, vcY_inj] at hy
          exact hxy ⟨rfl, hy⟩
        rw [Affine.Point.add_some hxy, vcPoint_some, vcPoint_some, vcPoint_some,
          Affine.Point.add_some hxy']
        exact some_ext (by rw [vcX_addX, slope_vc C W h₁.1 h₂.1 hxy])
          (by rw [vcY_addY, slope_vc C W h₁.1 h₂.1 hxy])

/-- The additive homomorphism `W(k) → (C • W)(k)`. -/
def vcHom : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := vcPoint C W
  map_zero' := rfl
  map_add' := vcPoint_add C W

@[simp] lemma vcHom_apply (P : W.toAffine.Point) : vcHom C W P = vcPoint C W P := rfl

lemma vcPoint_injective : Function.Injective (vcPoint C W) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hQ =>
      rw [vcPoint_some] at h
      change Affine.Point.zero = _ at h
      cases h
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      rw [vcPoint_some] at h
      change _ = Affine.Point.zero at h
      cases h
    | some x₂ y₂ h₂ =>
      rw [vcPoint_some, vcPoint_some, Affine.Point.some.injEq] at h
      obtain ⟨hx, hy⟩ := h
      have hx' := vcX_injective C hx
      subst hx'
      rw [vcY_inj] at hy
      subst hy
      rfl

lemma vcPoint_surjective : Function.Surjective (vcPoint C W) := by
  intro P'
  cases P' with
  | zero => exact ⟨0, rfl⟩
  | some x' y' h' =>
    have hx := vcX_of C x'
    have hy := vcY_of C x' y'
    have hns : W.toAffine.Nonsingular ((C.u : k) ^ 2 * x' + C.r)
        ((C.u : k) ^ 3 * y' + (C.u : k) ^ 2 * C.s * x' + C.t) := by
      rw [nonsingular_vc C W, hx, hy]
      exact h'
    exact ⟨.some _ _ hns, some_ext hx hy⟩

/-- **The additive isomorphism `W(k) ≃+ (C • W)(k)`** induced by a change of variables. -/
def vcEquiv : W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.ofBijective (vcHom C W) ⟨vcPoint_injective C W, vcPoint_surjective C W⟩

@[simp] lemma vcEquiv_apply (P : W.toAffine.Point) : vcEquiv C W P = vcPoint C W P := rfl

lemma vcEquiv_symm_apply (P' : (C • W).toAffine.Point) :
    vcPoint C W ((vcEquiv C W).symm P') = P' :=
  (vcEquiv C W).apply_symm_apply P'

/-! ### Coordinates of points -/

/-- The `x`-coordinate of a point (`0` at infinity). -/
def ptX {W : WeierstrassCurve k} : W.toAffine.Point → k
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point (`0` at infinity). -/
def ptY {W : WeierstrassCurve k} : W.toAffine.Point → k
  | .zero => 0
  | .some _ y _ => y

/-- Transport of points along an equality of curves. -/
def pointCongr {W W' : WeierstrassCurve k} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma ptX_pointCongr {W W' : WeierstrassCurve k} (h : W = W') (P : W.toAffine.Point) :
    ptX (pointCongr h P) = ptX P := by
  subst h
  rfl

@[simp] lemma ptY_pointCongr {W W' : WeierstrassCurve k} (h : W = W') (P : W.toAffine.Point) :
    ptY (pointCongr h P) = ptY P := by
  subst h
  rfl

@[simp] lemma ptX_pointCongr_symm {W W' : WeierstrassCurve k} (h : W = W')
    (P : W'.toAffine.Point) : ptX ((pointCongr h).symm P) = ptX P := by
  subst h
  rfl

@[simp] lemma ptY_pointCongr_symm {W W' : WeierstrassCurve k} (h : W = W')
    (P : W'.toAffine.Point) : ptY ((pointCongr h).symm P) = ptY P := by
  subst h
  rfl

end Points

end

end AbcAdaptation.Reference.Iut.Anabelian

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/UltrametricSqrt.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: adapted namespace and imports for Prove2Me
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# Square roots in complete ultrametric fields (Hensel's lemma, Babylonian form)

Let `k` be a complete non-archimedean normed field in which `‖2‖ = 1` (residue characteristic
different from `2`). If `x₀` is a unit (`‖x₀‖ = 1`) with `‖x₀ ^ 2 - a‖ < 1`, then `a` has a
square root `x` in `k` with `‖x - x₀‖ < 1`: this is Hensel's lemma for the polynomial
`X ^ 2 - a`, proved here directly by the Babylonian (Newton) iteration

`x (n + 1) = (x n + a / x n) / 2`,

which stays on the unit sphere and satisfies the exact identity

`(x (n + 1)) ^ 2 - a = ((x n) ^ 2 - a) ^ 2 / (4 * (x n) ^ 2)`,

so that `‖(x (n + 1)) ^ 2 - a‖ = ‖(x n) ^ 2 - a‖ ^ 2`. Consequently the defects
`‖(x n) ^ 2 - a‖` are bounded by `ε ^ (n + 1)` with `ε := ‖x₀ ^ 2 - a‖ < 1`, the increments
`x (n + 1) - x n = (a - (x n) ^ 2) / (2 * x n)` have the same norm as the defects, the sequence is
Cauchy, and its limit is the required square root.

## Main results

* `AbcAdaptation.Reference.Iut.babylonianSqrt`: the iteration.
* `AbcAdaptation.Reference.Iut.exists_sq_eq_of_norm_sq_sub_lt`: Hensel's lemma for square roots, with the bound
  `‖x - x₀‖ < 1` on the root.
* `AbcAdaptation.Reference.Iut.exists_sq_eq_of_norm_sub_one_lt`: every `a` with `‖a - 1‖ < 1` is a square.
-/

open Filter Topology

namespace AbcAdaptation.Reference.Iut

variable {k : Type*} [NormedField k]

/-- The Babylonian (Newton) iteration for a square root of `a`, started at `x₀`:
`x 0 = x₀` and `x (n + 1) = (x n + a / x n) / 2`. -/
noncomputable def babylonianSqrt (a x₀ : k) : ℕ → k
  | 0 => x₀
  | n + 1 => (babylonianSqrt a x₀ n + a / babylonianSqrt a x₀ n) / 2

@[simp]
theorem babylonianSqrt_zero (a x₀ : k) : babylonianSqrt a x₀ 0 = x₀ := rfl

theorem babylonianSqrt_succ (a x₀ : k) (n : ℕ) :
    babylonianSqrt a x₀ (n + 1) = (babylonianSqrt a x₀ n + a / babylonianSqrt a x₀ n) / 2 := rfl

/-- The exact one-step identity for the defect of the Babylonian iteration. -/
theorem babylonian_step_sq_sub (a x : k) (hx : x ≠ 0) (h2 : (2 : k) ≠ 0) :
    ((x + a / x) / 2) ^ 2 - a = (x ^ 2 - a) ^ 2 / (4 * x ^ 2) := by
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  field_simp
  ring

/-- The exact one-step identity for the increment of the Babylonian iteration. -/
theorem babylonian_step_sub (a x : k) (hx : x ≠ 0) (h2 : (2 : k) ≠ 0) :
    (x + a / x) / 2 - x = (a - x ^ 2) / (2 * x) := by
  field_simp
  ring

section Norms

variable (h2 : ‖(2 : k)‖ = 1)
include h2

theorem norm_four_eq_one : ‖(4 : k)‖ = 1 := by
  have : (4 : k) = 2 * 2 := by norm_num
  rw [this, norm_mul, h2, one_mul]

theorem two_ne_zero_of_norm_two_eq_one : (2 : k) ≠ 0 := by
  intro h
  rw [h, norm_zero] at h2
  exact zero_ne_one h2

/-- One step of the Babylonian iteration squares the defect (in norm). -/
theorem norm_babylonian_step_sq_sub (a : k) {x : k} (hx : ‖x‖ = 1) :
    ‖((x + a / x) / 2) ^ 2 - a‖ = ‖x ^ 2 - a‖ ^ 2 := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact zero_ne_one hx
  rw [babylonian_step_sq_sub a x hx0 (two_ne_zero_of_norm_two_eq_one h2), norm_div, norm_pow,
    norm_mul, norm_four_eq_one h2, norm_pow, hx, one_pow, one_mul, div_one]

/-- One step of the Babylonian iteration moves by exactly the norm of the defect. -/
theorem norm_babylonian_step_sub (a : k) {x : k} (hx : ‖x‖ = 1) :
    ‖(x + a / x) / 2 - x‖ = ‖x ^ 2 - a‖ := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact zero_ne_one hx
  rw [babylonian_step_sub a x hx0 (two_ne_zero_of_norm_two_eq_one h2), norm_div, norm_mul, h2, hx,
    one_mul, div_one, norm_sub_rev]

variable [IsUltrametricDist k]

omit h2 in
/-- In an ultrametric normed field, a perturbation of a unit by an element of norm `< 1` is
again a unit. -/
theorem norm_eq_one_of_norm_sub_lt_one {x y : k} (hx : ‖x‖ = 1) (h : ‖y - x‖ < 1) : ‖y‖ = 1 := by
  have hy : y = x + (y - x) := by ring
  have hne : ‖x‖ ≠ ‖y - x‖ := by
    rw [hx]
    exact h.ne'
  rw [hy, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hx, max_eq_left h.le]

/-- Along the Babylonian iteration started at a unit `x₀` with `‖x₀ ^ 2 - a‖ < 1`, every term
is a unit and the defect at stage `n` is at most `‖x₀ ^ 2 - a‖ ^ (n + 1)`. -/
theorem babylonianSqrt_norm_eq_one_and_norm_sq_sub_le {a x₀ : k} (hx₀ : ‖x₀‖ = 1)
    (h : ‖x₀ ^ 2 - a‖ < 1) (n : ℕ) :
    ‖babylonianSqrt a x₀ n‖ = 1 ∧
      ‖babylonianSqrt a x₀ n ^ 2 - a‖ ≤ ‖x₀ ^ 2 - a‖ ^ (n + 1) := by
  set ε := ‖x₀ ^ 2 - a‖ with hε
  have hε0 : 0 ≤ ε := norm_nonneg _
  have hε1 : ε ≤ 1 := h.le
  induction n with
  | zero =>
    refine ⟨hx₀, ?_⟩
    simp [hε]
  | succ n ih =>
    obtain ⟨hn, hb⟩ := ih
    have hstep : ‖babylonianSqrt a x₀ (n + 1) ^ 2 - a‖ = ‖babylonianSqrt a x₀ n ^ 2 - a‖ ^ 2 := by
      rw [babylonianSqrt_succ]
      exact norm_babylonian_step_sq_sub h2 a hn
    have hinc : ‖babylonianSqrt a x₀ (n + 1) - babylonianSqrt a x₀ n‖ =
        ‖babylonianSqrt a x₀ n ^ 2 - a‖ := by
      rw [babylonianSqrt_succ]
      exact norm_babylonian_step_sub h2 a hn
    have hlt : ‖babylonianSqrt a x₀ (n + 1) - babylonianSqrt a x₀ n‖ < 1 := by
      rw [hinc]
      calc ‖babylonianSqrt a x₀ n ^ 2 - a‖ ≤ ε ^ (n + 1) := hb
        _ < 1 := pow_lt_one₀ hε0 h n.succ_ne_zero
    refine ⟨norm_eq_one_of_norm_sub_lt_one hn hlt, ?_⟩
    calc ‖babylonianSqrt a x₀ (n + 1) ^ 2 - a‖
        = ‖babylonianSqrt a x₀ n ^ 2 - a‖ ^ 2 := hstep
      _ ≤ (ε ^ (n + 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = ε ^ (2 * (n + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ ε ^ (n + 1 + 1) := pow_le_pow_of_le_one hε0 hε1 (by
        calc
          n + 1 + 1 = (n + 1) + 1 := rfl
          _ ≤ (n + 1) + (n + 1) := Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le n)) _
          _ = 2 * (n + 1) := by rw [Nat.two_mul])

/-- Along the Babylonian iteration, every term stays within `‖x₀ ^ 2 - a‖` of `x₀`. -/
theorem norm_babylonianSqrt_sub_le {a x₀ : k} (hx₀ : ‖x₀‖ = 1) (h : ‖x₀ ^ 2 - a‖ < 1) (n : ℕ) :
    ‖babylonianSqrt a x₀ n - x₀‖ ≤ ‖x₀ ^ 2 - a‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hn, hb⟩ := babylonianSqrt_norm_eq_one_and_norm_sq_sub_le h2 hx₀ h n
    have hinc : ‖babylonianSqrt a x₀ (n + 1) - babylonianSqrt a x₀ n‖ ≤ ‖x₀ ^ 2 - a‖ := by
      rw [babylonianSqrt_succ, norm_babylonian_step_sub h2 a hn]
      calc ‖babylonianSqrt a x₀ n ^ 2 - a‖ ≤ ‖x₀ ^ 2 - a‖ ^ (n + 1) := hb
        _ ≤ ‖x₀ ^ 2 - a‖ := pow_le_of_le_one (norm_nonneg _) h.le n.succ_ne_zero
    have hsplit : babylonianSqrt a x₀ (n + 1) - x₀ =
        (babylonianSqrt a x₀ (n + 1) - babylonianSqrt a x₀ n) + (babylonianSqrt a x₀ n - x₀) := by
      ring
    rw [hsplit]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hinc ih)

end Norms

variable [IsUltrametricDist k] [CompleteSpace k]

/-- **Hensel's lemma for square roots** in a complete ultrametric field with `‖2‖ = 1`: an
approximate square root `x₀` of `a` on the unit sphere with `‖x₀ ^ 2 - a‖ < 1` refines to an
exact square root `x` with `‖x - x₀‖ < 1`. -/
theorem exists_sq_eq_of_norm_sq_sub_lt (h2 : ‖(2 : k)‖ = 1) {a x₀ : k} (hx₀ : ‖x₀‖ = 1)
    (h : ‖x₀ ^ 2 - a‖ < 1) : ∃ x : k, x ^ 2 = a ∧ ‖x - x₀‖ < 1 := by
  set ε := ‖x₀ ^ 2 - a‖ with hε
  have hε0 : 0 ≤ ε := norm_nonneg _
  set u : ℕ → k := babylonianSqrt a x₀ with hu
  have hbound : ∀ n, ‖u n ^ 2 - a‖ ≤ ε ^ (n + 1) := fun n =>
    (babylonianSqrt_norm_eq_one_and_norm_sq_sub_le h2 hx₀ h n).2
  have hunit : ∀ n, ‖u n‖ = 1 := fun n =>
    (babylonianSqrt_norm_eq_one_and_norm_sq_sub_le h2 hx₀ h n).1
  -- the sequence is Cauchy
  have hdist : ∀ n, dist (u n) (u (n + 1)) ≤ ε * ε ^ n := by
    intro n
    rw [dist_eq_norm, norm_sub_rev, hu, babylonianSqrt_succ, norm_babylonian_step_sub h2 a (hunit n),
      ← pow_succ']
    exact hbound n
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric ε ε h hdist
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x, ?_, ?_⟩
  · -- the limit is a square root of `a`
    have h1 : Tendsto (fun n => u n ^ 2 - a) atTop (𝓝 (x ^ 2 - a)) := (hx.pow 2).sub_const a
    have hpow : Tendsto (fun n : ℕ => ε ^ (n + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hε0 h).comp (tendsto_add_atTop_nat 1)
    have h0 : Tendsto (fun n => u n ^ 2 - a) atTop (𝓝 0) :=
      squeeze_zero_norm hbound hpow
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h0)
  · -- the limit stays within `ε < 1` of `x₀`
    have hlim : Tendsto (fun n => ‖u n - x₀‖) atTop (𝓝 ‖x - x₀‖) := (hx.sub_const x₀).norm
    have hle : ‖x - x₀‖ ≤ ε :=
      le_of_tendsto' hlim fun n => norm_babylonianSqrt_sub_le h2 hx₀ h n
    exact hle.trans_lt h

/-- In a complete ultrametric field with `‖2‖ = 1`, every element of the open unit ball around
`1` is a square. -/
theorem exists_sq_eq_of_norm_sub_one_lt (h2 : ‖(2 : k)‖ = 1) {a : k} (ha : ‖a - 1‖ < 1) :
    ∃ x : k, x ^ 2 = a := by
  have h : ‖(1 : k) ^ 2 - a‖ < 1 := by
    rw [one_pow, norm_sub_rev]
    exact ha
  obtain ⟨x, hx, -⟩ := exists_sq_eq_of_norm_sq_sub_lt h2 norm_one h
  exact ⟨x, hx⟩

end AbcAdaptation.Reference.Iut

/-
Adapted from Iut/Cor312/ThetaData/BadPlaceNorm.lean,
Iut/Cor312/ThetaData/SqrtAtBadPlace.lean, Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean,
and Iut/Cor312/ThetaData/TateIsomorphism.lean.
Source snapshot 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8, lana-agents/iut.
Upstream commits cfc9e36c8984a83c9199ccbb8d1b30d9c130edf6,
e4777b2238f45be2e58c00b4d0213c0cb83405b9 and 09d74a40f46688fa5e4eba46ead73cb37d6abbe2.
Git author Christian Merten.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve IsDedekindDomain.HeightOneSpectrum TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

section Tangent

variable {k : Type*} [NormedField k]

/-- The tangent quadratic obtained from the coefficients of the Weierstrass equation. -/
def tangentQuadratic (W : WeierstrassCurve k) (r : k) : k :=
  W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

lemma tangent_sq_eq (W : WeierstrassCurve k) (r : k) :
    (2 * W.c₄ * r + W.a₁ * W.c₄) ^ 2 =
      -(W.c₄ * W.c₆) + 4 * W.c₄ * tangentQuadratic W r := by
  simp only [tangentQuadratic, c₄, c₆, b₂, b₄, b₆]
  ring

lemma exists_tangent_root_of_sq (W : WeierstrassCurve k) (h2 : (2 : k) ≠ 0)
    (hc₄ : W.c₄ ≠ 0) {s : k} (hs : s ^ 2 = -(W.c₄ * W.c₆)) :
    ∃ r : k, ‖tangentQuadratic W r‖ < 1 := by
  let r := (s - W.a₁ * W.c₄) / (2 * W.c₄)
  refine ⟨r, ?_⟩
  have hr : 2 * W.c₄ * r + W.a₁ * W.c₄ = s := by
    change 2 * W.c₄ * ((s - W.a₁ * W.c₄) / (2 * W.c₄)) + W.a₁ * W.c₄ = s
    rw [mul_div_cancel₀ _ (mul_ne_zero h2 hc₄)]
    exact sub_add_cancel _ _
  have h := tangent_sq_eq W r
  rw [hr, hs] at h
  have hzero : -(W.c₄ * W.c₆) + 4 * W.c₄ * tangentQuadratic W r =
      -(W.c₄ * W.c₆) + 0 := by
    rw [add_zero]
    exact h.symm
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hf := (mul_eq_zero.mp (add_left_cancel hzero)).resolve_left (mul_ne_zero h4 hc₄)
  rw [hf, norm_zero]
  exact zero_lt_one

lemma sq_neg_c₄_mul_c₆_variableChange (W : WeierstrassCurve k) (C : VariableChange k)
    {s : k} (hs : s ^ 2 = -(W.c₄ * W.c₆)) :
    (((C.u⁻¹ : kˣ) : k) ^ 5 * s) ^ 2 = -((C • W).c₄ * (C • W).c₆) := by
  rw [mul_pow, hs, variableChange_c₄, variableChange_c₆]
  ring

/-- The norm of the j-invariant of a multiplicative model is greater than one. -/
lemma one_lt_norm_j_of_norms (W : WeierstrassCurve k) [W.IsElliptic]
    (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) : 1 < ‖W.j‖ := by
  have hΔ0 : W.Δ ≠ 0 := by
    rw [← coe_Δ']
    exact W.Δ'.ne_zero
  rw [j, Units.val_inv_eq_inv_val, coe_Δ', norm_mul, norm_inv, norm_pow, hc₄, one_pow, mul_one]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hΔ0)).mpr hΔ

end Tangent

section Completions

variable {F : Type u} [Field F] [NumberField F]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (E : WeierstrassCurve F) (K : IntermediateField F Fbar) [NumberField ↥K]

lemma curveKw_variableChange (C : VariableChange F) (w : FinitePlace ↥K) :
    curveKw (C • E) K w = ((C.map (algebraMap F ↥K)).map (emb K w)) • curveKw E K w := by
  rw [curveKw, curveK, map_variableChange, map_variableChange]

lemma neg_c₄_mul_c₆_curveKw (w : FinitePlace ↥K) :
    -((curveKw E K w).c₄ * (curveKw E K w).c₆) =
      emb K w (algebraMap F ↥K (-(E.c₄ * E.c₆))) := by
  simp only [curveKw, curveK, map_c₄, map_c₆, map_neg, map_mul]

variable {w : FinitePlace ↥K} {v : FinitePlace F}

lemma norm_c₄_curveKw (hwv : FinitePlace.LiesOver w v)
    (hc₄ : v.maximalIdeal.valuation F E.c₄ = 1) :
    ‖(curveKw E K w).c₄‖ = 1 := by
  rw [curveKw, curveK, map_c₄, map_c₄, emb, norm_eq_one_iff_valued,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    Tripod.valuation_algebraMap_eq_pow hwv, hc₄, one_pow]

lemma norm_Δ_curveKw (hwv : FinitePlace.LiesOver w v)
    (hΔ : v.maximalIdeal.valuation F E.Δ < 1) :
    ‖(curveKw E K w).Δ‖ < 1 := by
  rw [curveKw, curveK, map_Δ, map_Δ, emb, norm_lt_one_iff_valued,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    Tripod.valuation_algebraMap_eq_pow hwv]
  exact pow_lt_one₀ zero_le hΔ (Tripod.ramificationIdx'_ne_zero hwv)

variable [E.IsElliptic] {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

lemma mult_placeUnder
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    (hw : IsBadPlace E K VBad w) :
    HasMultiplicativeReductionAt E (Tripod.placeUnder w : FinitePlace F) := by
  obtain ⟨v, hv, hwv⟩ := hw
  refine hmult v hv _ ⟨?_⟩
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  rw [hwv.over, Tripod.placeUnder_maximalIdeal, Ideal.under_def, Ideal.under_def,
    Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]

lemma norm_two_curveKw (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hw : IsBadPlace E K VBad w) : ‖(2 : localCompletion w)‖ = 1 := by
  obtain ⟨v, hv, hwv⟩ := hw
  have h2 : residueChar w ≠ 2 := fun h =>
    hVBad v hv ((Tripod.residueChar_eq_of_liesOver hwv).symm.trans h)
  have hcast : (2 : localCompletion w) = emb K w (2 : ↥K) := by rw [map_ofNat]
  rw [hcast, emb, norm_eq_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation']
  exact Tripod.valuation_two_eq_one_of_ne h2

end Completions

end

end AbcAdaptation.Reference.Iut

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/TateIsomorphism.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: adapted namespace and imports for Prove2Me and reused the local Tate parameter and norm lemmas
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# Tate's isomorphism theorem: split multiplicative curves are Tate curves

Over a complete ultrametric field `k` with `‖2‖ = 1` (residue characteristic `≠ 2`) and
`12 ≠ 0`, an
elliptic curve `W` with `‖c₄‖ = 1`, `‖Δ‖ < 1` (multiplicative reduction) whose tangent quadratic
at the node has a root modulo the maximal ideal (split reduction) is isomorphic over `k` to the
Tate curve `E_q` of the unique Tate parameter `q` with `j(E_q) = j(W)` (Silverman, *Advanced
Topics*, V.5.3). The argument:

* `‖j(W)‖ > 1`, so `q` exists (`TateCurvesTheta`, `exists_tateParameter_tateJ_eq`);
* both curves have short Weierstrass normal forms `y² = x³ + ax + b`, `y² = x³ + a'x + b'`
  (Mathlib, `exists_variableChange_isShortNF`), and equal `j` gives `a'³b² = a³b'²`, so the two
  normal forms differ by the scaling `u` with `u² = λ := a'b/(ab')`
  (`AbcAdaptation.Reference.Iut.exists_scaleChange_of_j_eq`) — provided `λ` is a square;
* `λ` is, up to visible squares, the ratio `c₄c₆(W)/c₄c₆(E_q)`, and both `−c₄c₆(W)` and
  `−c₄c₆(E_q)` are units congruent to squares modulo the maximal ideal: for `W` because
  `−c₄c₆` is the discriminant of the tangent quadratic, for `E_q` because `c₄ ≡ 1`, `c₆ ≡ −1`;
  Hensel's lemma (`AbcAdaptation.Reference.Iut.exists_sq_eq_of_norm_sq_sub_lt`) then makes the ratio a square.
-/

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve TateCurvesTheta

noncomputable section

variable {k : Type*} [NormedField k]

/-- The scaling change of variables `(u, 0, 0, 0)`. -/
def scaleChange (u : kˣ) : VariableChange k := ⟨u, 0, 0, 0⟩

section ShortNF

variable (W₁ W₂ : WeierstrassCurve k) [W₁.IsShortNF] [W₂.IsShortNF]

/-- A scaling carries one short normal form to another when the coefficients match. -/
lemma scaleChange_smul_eq (u : kˣ) (h4 : W₂.a₄ = (u : k)⁻¹ ^ 4 * W₁.a₄)
    (h6 : W₂.a₆ = (u : k)⁻¹ ^ 6 * W₁.a₆) : scaleChange u • W₁ = W₂ := by
  ext
  · rw [variableChange_a₁, a₁_of_isShortNF, a₁_of_isShortNF]
    simp [scaleChange]
  · rw [variableChange_a₂, a₂_of_isShortNF, a₂_of_isShortNF, a₁_of_isShortNF]
    simp [scaleChange]
  · rw [variableChange_a₃, a₃_of_isShortNF, a₃_of_isShortNF, a₁_of_isShortNF]
    simp [scaleChange]
  · rw [variableChange_a₄, a₃_of_isShortNF, a₂_of_isShortNF, a₁_of_isShortNF, h4]
    simp [scaleChange]
  · rw [variableChange_a₆, a₃_of_isShortNF, a₂_of_isShortNF, a₁_of_isShortNF, h6]
    simp [scaleChange]

variable [IsUltrametricDist k] [W₁.IsElliptic] [W₂.IsElliptic]

private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : k)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one k _

/-- In a short normal form with non-integral `j`, both coefficients are nonzero. -/
lemma coeff_ne_zero_of_isShortNF (h2 : (2 : k) ≠ 0) (hj : 1 < ‖W₁.j‖) :
    W₁.a₄ ≠ 0 ∧ W₁.a₆ ≠ 0 := by
  have hΔ : W₁.Δ ≠ 0 := by rw [← coe_Δ']; exact W₁.Δ'.ne_zero
  have hD : 4 * W₁.a₄ ^ 3 + 27 * W₁.a₆ ^ 2 ≠ 0 := by
    intro h
    apply hΔ
    rw [Δ_of_isShortNF, h, mul_zero]
  have hjeq := W₁.j_of_isShortNF
  constructor
  · intro ha
    rw [hjeq, ha] at hj
    norm_num at hj
  · intro hb
    rw [hjeq, hb] at hj
    have ha : W₁.a₄ ≠ 0 := by
      intro ha
      apply hD
      rw [ha, hb]
      ring
    have h4 : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_ne_zero _ h2
    have : (6912 * W₁.a₄ ^ 3 / (4 * W₁.a₄ ^ 3 + 27 * 0 ^ 2) : k) = 1728 := by
      field_simp
      ring
    rw [this] at hj
    exact absurd hj (not_lt.mpr (norm_ofNat_le_one 1728))

/-- **Short normal forms with equal `j`-invariant differ by a scaling** `u` with
`u² = a'b/(ab')`, provided that ratio is a square. -/
theorem exists_scaleChange_of_j_eq (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hj1 : 1 < ‖W₁.j‖) (hj : W₁.j = W₂.j)
    (hsq : IsSquare ((W₂.a₄ * W₁.a₆) / (W₁.a₄ * W₂.a₆))) :
    ∃ u : kˣ, scaleChange u • W₁ = W₂ := by
  obtain ⟨ha, hb⟩ := coeff_ne_zero_of_isShortNF W₁ h2 hj1
  obtain ⟨ha', hb'⟩ := coeff_ne_zero_of_isShortNF W₂ h2 (hj ▸ hj1)
  have hD : 4 * W₁.a₄ ^ 3 + 27 * W₁.a₆ ^ 2 ≠ 0 := by
    intro h
    have hΔ : W₁.Δ ≠ 0 := by rw [← coe_Δ']; exact W₁.Δ'.ne_zero
    exact hΔ (by rw [Δ_of_isShortNF, h, mul_zero])
  have hD' : 4 * W₂.a₄ ^ 3 + 27 * W₂.a₆ ^ 2 ≠ 0 := by
    intro h
    have hΔ : W₂.Δ ≠ 0 := by rw [← coe_Δ']; exact W₂.Δ'.ne_zero
    exact hΔ (by rw [Δ_of_isShortNF, h, mul_zero])
  -- the key relation `a'³ b² = a³ b'²`
  have key : W₂.a₄ ^ 3 * W₁.a₆ ^ 2 = W₁.a₄ ^ 3 * W₂.a₆ ^ 2 := by
    have h := hj
    rw [W₁.j_of_isShortNF, W₂.j_of_isShortNF, div_eq_div_iff hD hD'] at h
    have hc : (6912 * 27 : k) ≠ 0 := by
      have : (6912 * 27 : k) = 2 ^ 8 * 3 ^ 6 := by norm_num
      rw [this]
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
    apply mul_left_cancel₀ hc
    linear_combination -h
  obtain ⟨u₀, hu₀⟩ := hsq
  set lam := (W₂.a₄ * W₁.a₆) / (W₁.a₄ * W₂.a₆) with hlam
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    exact div_ne_zero (mul_ne_zero ha' hb) (mul_ne_zero ha hb')
  have hu₀0 : u₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu₀
    exact hlam0 hu₀
  -- `a' λ² = a` and `b' λ³ = b`
  have h4 : W₂.a₄ * lam ^ 2 = W₁.a₄ := by
    rw [hlam, div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero _ (mul_ne_zero ha hb'))]
    linear_combination key
  have h6 : W₂.a₆ * lam ^ 3 = W₁.a₆ := by
    rw [hlam, div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero _ (mul_ne_zero ha hb'))]
    linear_combination W₁.a₆ * W₂.a₆ * key
  refine ⟨Units.mk0 u₀ hu₀0, scaleChange_smul_eq W₁ W₂ _ ?_ ?_⟩
  · rw [Units.val_mk0, show (u₀⁻¹) ^ 4 = ((u₀ * u₀)⁻¹) ^ 2 by ring, ← hu₀, ← h4]
    field_simp
  · rw [Units.val_mk0, show (u₀⁻¹) ^ 6 = ((u₀ * u₀)⁻¹) ^ 3 by ring, ← hu₀, ← h6]
    field_simp

end ShortNF

/-! ## The isomorphism theorem -/

section Main

variable [IsUltrametricDist k] [CompleteSpace k]

omit [CompleteSpace k] in
private lemma norm_ofNat_le_one' (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : k)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one k _

omit [IsUltrametricDist k] [CompleteSpace k] in
private lemma norm_mul_lt_one_of_le_of_lt {a b : k} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ < 1) :
    ‖a * b‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg b]

omit [IsUltrametricDist k] [CompleteSpace k] in
private lemma norm_mul_lt_one_of_lt_of_le {a b : k} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg b]

omit [CompleteSpace k] in
/-- `‖x + y‖ = ‖x‖` when `‖y‖ < ‖x‖`. -/
private lemma norm_add_eq_left {x y : k} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

omit [CompleteSpace k] in
/-- `‖c₆‖ = 1` for a curve with `‖c₄‖ = 1`, `‖Δ‖ < 1`. -/
lemma norm_c₆_eq_one (W : WeierstrassCurve k) (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) :
    ‖W.c₆‖ = 1 := by
  have h : W.c₆ ^ 2 = W.c₄ ^ 3 + -(1728 * W.Δ) := by
    have hc := W.c_relation
    linear_combination hc
  have hn : ‖W.c₆ ^ 2‖ = 1 := by
    rw [h, norm_add_eq_left, norm_pow, hc₄, one_pow]
    rw [norm_pow, hc₄, one_pow, norm_neg]
    exact norm_mul_lt_one_of_le_of_lt (norm_ofNat_le_one' 1728) hΔ
  rw [norm_pow] at hn
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hn

omit [IsUltrametricDist k] [CompleteSpace k] in
/-- `c₆(E_q) = −1 + 72 a₄ − 864 a₆`. -/
lemma tateCurve_c₆ (t : TateParameter k) : t.tateCurve.c₆ = -1 + 72 * t.a₄ - 864 * t.a₆ := by
  simp only [c₆, t.tateCurve_b₂, t.tateCurve_b₄, t.tateCurve_b₆]
  ring

/-- `c₄c₆(E_q) ≡ −1` modulo the maximal ideal. -/
lemma norm_tateCurve_c₄_mul_c₆_add_one_lt (t : TateParameter k) (h12 : (12 : k) ≠ 0) :
    ‖t.tateCurve.c₄ * t.tateCurve.c₆ + 1‖ < 1 := by
  have h4 := t.norm_a₄_le.trans_lt t.norm_lt_one
  have h6 := (t.norm_a₆_le h12).trans_lt t.norm_lt_one
  have : t.tateCurve.c₄ * t.tateCurve.c₆ + 1 =
      t.a₄ * (120 - 3456 * t.a₄ + 41472 * t.a₆) + (-864) * t.a₆ := by
    rw [t.tateCurve_c₄_eq, tateCurve_c₆]
    ring
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · refine norm_mul_lt_one_of_lt_of_le h4 ?_
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_ofNat_le_one' 120) ?_)
      rw [norm_neg, norm_mul]
      exact mul_le_one₀ (norm_ofNat_le_one' 3456) (norm_nonneg _) h4.le
    · rw [norm_mul]
      exact mul_le_one₀ (norm_ofNat_le_one' 41472) (norm_nonneg _) h6.le
  · rw [norm_mul, norm_neg]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_ofNat_le_one' 864) (norm_nonneg _) h6

/-- **The ratio `c₄c₆(W)/c₄c₆(E_q)` is a square** when the tangent quadratic of `W` at its node
has a root modulo the maximal ideal. -/
lemma isSquare_ratio (h12 : (12 : k) ≠ 0)
    (hsqrt : ∀ a x₀ : k, ‖x₀‖ = 1 → ‖x₀ ^ 2 - a‖ < 1 → ∃ x, x ^ 2 = a)
    (W : WeierstrassCurve k) (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1)
    (hroot : ∃ r : k, ‖tangentQuadratic W r‖ < 1)
    (t : TateParameter k) :
    IsSquare ((W.c₄ * W.c₆) / (t.tateCurve.c₄ * t.tateCurve.c₆)) := by
  obtain ⟨r, hr⟩ := hroot
  have hc₆ := norm_c₆_eq_one W hc₄ hΔ
  set s := 2 * W.c₄ * r + W.a₁ * W.c₄ with hs
  set ε₁ := 4 * W.c₄ * tangentQuadratic W r with hε₁
  have hs2 : s ^ 2 = -(W.c₄ * W.c₆) + ε₁ := tangent_sq_eq W r
  have hε₁n : ‖ε₁‖ < 1 := by
    rw [hε₁, mul_assoc]
    refine norm_mul_lt_one_of_le_of_lt (norm_ofNat_le_one' 4) ?_
    exact norm_mul_lt_one_of_le_of_lt hc₄.le hr
  have hDW : ‖W.c₄ * W.c₆‖ = 1 := by rw [norm_mul, hc₄, hc₆, one_mul]
  have hsn : ‖s‖ = 1 := by
    have : ‖s ^ 2‖ = 1 := by
      rw [hs2, norm_add_eq_left, norm_neg, hDW]
      rw [norm_neg, hDW]
      exact hε₁n
    rw [norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  set ε₂ := t.tateCurve.c₄ * t.tateCurve.c₆ + 1 with hε₂
  have hε₂n : ‖ε₂‖ < 1 := norm_tateCurve_c₄_mul_c₆_add_one_lt t h12
  have hD' : t.tateCurve.c₄ * t.tateCurve.c₆ = -1 + ε₂ := by rw [hε₂]; ring
  have hden : ‖(-1 : k) + ε₂‖ = 1 := by
    rw [norm_add_eq_left] <;> rw [norm_neg, norm_one]
    exact hε₂n
  have hden0 : (-1 : k) + ε₂ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    exact zero_ne_one hden
  set μ := (W.c₄ * W.c₆) / (t.tateCurve.c₄ * t.tateCurve.c₆) with hμ
  have key : s ^ 2 - μ = (-(W.c₄ * W.c₆) * ε₂ - ε₁ + ε₁ * ε₂) / (-1 + ε₂) := by
    rw [hμ, hD', hs2]
    field_simp
    ring
  have hlt : ‖s ^ 2 - μ‖ < 1 := by
    rw [key, norm_div, hden, div_one]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul, norm_neg, hDW, one_mul]
        exact hε₂n
      · rw [norm_neg]
        exact hε₁n
    · exact norm_mul_lt_one_of_lt_of_le hε₁n hε₂n.le
  obtain ⟨m, hm⟩ := hsqrt μ s hsn hlt
  exact ⟨m, by rw [← hm, sq]⟩

/-- **Tate's isomorphism theorem.** An elliptic curve `W` over `k` with `‖c₄‖ = 1`, `‖Δ‖ < 1` whose
tangent quadratic at the node has a root modulo the maximal ideal is, after a change of
variables, the Tate curve `E_q` of a Tate parameter `q` (with `j(E_q) = j(W)`). -/
theorem exists_variableChange_tateCurve (h2 : ‖(2 : k)‖ = 1) (h12 : (12 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1)
    (hroot : ∃ r : k, ‖tangentQuadratic W r‖ < 1) :
    ∃ (t : TateParameter k) (C : VariableChange k), C • W = t.tateCurve ∧ t.tateJ = W.j := by
  have hsqrt : ∀ a x₀ : k, ‖x₀‖ = 1 → ‖x₀ ^ 2 - a‖ < 1 → ∃ x, x ^ 2 = a := fun a x₀ hx h =>
    (exists_sq_eq_of_norm_sq_sub_lt h2 hx h).imp fun x hx => hx.1
  have h12ne : (12 : k) ≠ 0 := h12
  have h2ne : (2 : k) ≠ 0 := by
    intro h
    apply h12ne
    rw [show (12 : k) = 2 * 6 by norm_num, h, zero_mul]
  have h3ne : (3 : k) ≠ 0 := by
    intro h
    apply h12ne
    rw [show (12 : k) = 3 * 4 by norm_num, h, zero_mul]
  have hj := one_lt_norm_j_of_norms W hc₄ hΔ
  obtain ⟨t, ht⟩ := TateParameter.exists_tateParameter_tateJ_eq h12 hj
  haveI : t.tateCurve.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (t.tateCurve_Δ_ne_zero h12)⟩
  have hjE' : t.tateCurve.j = W.j := by
    rw [← ht, TateParameter.tateJ_def, j, Units.val_inv_eq_inv_val, coe_Δ', div_eq_mul_inv, mul_comm]
  letI := invertibleOfNonzero h2ne
  letI := invertibleOfNonzero h3ne
  obtain ⟨C₁, hC₁⟩ := W.exists_variableChange_isShortNF
  obtain ⟨C₂, hC₂⟩ := t.tateCurve.exists_variableChange_isShortNF
  have hj₁ : 1 < ‖(C₁ • W).j‖ := by rw [variableChange_j]; exact hj
  have hj₁₂ : (C₁ • W).j = (C₂ • t.tateCurve).j := by
    rw [variableChange_j, variableChange_j, hjE']
  -- the ratio `a'b/(ab')` of the normal forms is a square
  have hsq : IsSquare (((C₂ • t.tateCurve).a₄ * (C₁ • W).a₆) /
      ((C₁ • W).a₄ * (C₂ • t.tateCurve).a₆)) := by
    obtain ⟨m, hm⟩ := isSquare_ratio h12ne hsqrt W hc₄ hΔ hroot t
    have hc₄' : t.tateCurve.c₄ ≠ 0 := by
      intro h
      have := t.norm_tateCurve_c₄
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hc₆' : t.tateCurve.c₆ ≠ 0 := by
      intro h
      have := norm_c₆_eq_one t.tateCurve t.norm_tateCurve_c₄
        (by rw [t.norm_tateCurve_Δ h12ne]; exact t.norm_lt_one)
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hc₄0 : W.c₄ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc₄
      exact zero_ne_one hc₄
    have hc₆0 : W.c₆ ≠ 0 := by
      intro h
      have := norm_c₆_eq_one W hc₄ hΔ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have h48 : (48 : k) ≠ 0 := by
      have : (48 : k) = 2 ^ 4 * 3 := by norm_num
      rw [this]
      exact mul_ne_zero (pow_ne_zero _ h2ne) h3ne
    have h864 : (864 : k) ≠ 0 := by
      have : (864 : k) = 2 ^ 5 * 3 ^ 3 := by norm_num
      rw [this]
      exact mul_ne_zero (pow_ne_zero _ h2ne) (pow_ne_zero _ h3ne)
    have e₁ : (C₁ • W).a₄ = -(C₁ • W).c₄ / 48 := by
      rw [c₄_of_isShortNF]
      field_simp
    have e₂ : (C₁ • W).a₆ = -(C₁ • W).c₆ / 864 := by
      rw [c₆_of_isShortNF]
      field_simp
    have e₃ : (C₂ • t.tateCurve).a₄ = -(C₂ • t.tateCurve).c₄ / 48 := by
      rw [c₄_of_isShortNF]
      field_simp
    have e₄ : (C₂ • t.tateCurve).a₆ = -(C₂ • t.tateCurve).c₆ / 864 := by
      rw [c₆_of_isShortNF]
      field_simp
    refine ⟨(C₂.u : k) * t.tateCurve.c₄ * m / ((C₁.u : k) * W.c₄), ?_⟩
    rw [e₁, e₂, e₃, e₄, variableChange_c₄, variableChange_c₆, variableChange_c₄,
      variableChange_c₆, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    have hu₁ := C₁.u.ne_zero
    have hu₂ := C₂.u.ne_zero
    rw [div_eq_iff (mul_ne_zero hc₄' hc₆')] at hm
    field_simp
    linear_combination hm
  haveI := hC₁
  haveI := hC₂
  obtain ⟨u, hu⟩ := exists_scaleChange_of_j_eq (C₁ • W) (C₂ • t.tateCurve) h2ne h3ne hj₁ hj₁₂ hsq
  refine ⟨t, C₂⁻¹ * (scaleChange u * C₁), ?_, ht⟩
  rw [mul_smul, mul_smul, hu, inv_smul_smul]

end Main

end

end AbcAdaptation.Reference.Iut

/-
Adapted from TateCurvesTheta/TateCurve/PointMap.lean, GroupLaw.lean,
and TateUniformization.lean, lana-agents/tate-curves-theta at
ca6c2279d3cea0690cdb01328e727118d5485d68.
The point map uses the adapted Tate series. Its affine equation, additivity
and surjectivity are the analytic inputs.
-/
/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/

namespace AbcAdaptation.Reference

open WeierstrassCurve Iut.Anabelian
open scoped Classical

noncomputable section

namespace Iut

open TateCurvesTheta
variable {k : Type*} [NormedField k]

/-- The uniformization of the curve defined by a Tate parameter, with its affine coordinate laws. -/
structure TateParameterUniformization (t : TateParameter k) where
  iso : Additive (kˣ ⧸ Subgroup.zpowers t.q) ≃+ t.tateCurve.toAffine.Point
  iso_x : ∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * u ≠ 1) →
    ptX (iso (Additive.ofMul (QuotientGroup.mk u))) = t.X u
  iso_y : ∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * u ≠ 1) →
    ptY (iso (Additive.ofMul (QuotientGroup.mk u))) = t.Y u

variable [CompleteSpace k] [IsUltrametricDist k]

private def uniformizeTateParameter
    (t : TateParameter k) (h12 : (12 : k) ≠ 0) (h2 : ‖(2 : k)‖ = 1) :
    TateParameterUniformization t := by
  let h := exists_tateUniformization t h12 h2
  refine ⟨h.choose, ?_, ?_⟩
  · intro u hu
    have hx := h.choose_spec.1 u hu
    cases hp : h.choose (Additive.ofMul (QuotientGroup.mk u)) <;>
      simpa only [ptX, hp] using hx
  · intro u hu
    have hy := h.choose_spec.2 u hu
    cases hp : h.choose (Additive.ofMul (QuotientGroup.mk u)) <;>
      simpa only [ptY, hp] using hy

end Iut

end

end AbcAdaptation.Reference

/-
Adapted from Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean,
Iut/Cor312/ThetaData/TateStructureOfIso.lean and Iut/Cor312/ThetaData/TateStructure.lean.
Source snapshot 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8, lana-agents/iut.
Upstream commits e4777b2238f45be2e58c00b4d0213c0cb83405b9,
09d74a40f46688fa5e4eba46ead73cb37d6abbe2 and 76c7866b5bbc4adbd245a30af1a4fd05d32f8c3f,
respectively. Git author Christian Merten.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve Anabelian TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

section Transport

variable {k : Type*} [Field k] {W : WeierstrassCurve k}

lemma xCoord_eq_ptX (C : VariableChange k) (P : W.toAffine.Point) :
    xCoord C P = ptX (vcPoint C W P) := by
  cases P <;> rfl

lemma yCoord_eq_ptY (C : VariableChange k) (P : W.toAffine.Point) :
    yCoord C P = ptY (vcPoint C W P) := by
  cases P <;> rfl

variable [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

/-- Carry the uniformization and its coordinate laws along the change of model. -/
def TateStructure.ofVariableChangeWithUniformization
    (t : TateParameter k) (C : VariableChange k) (hC : C • W = t.tateCurve)
    (U : TateParameterUniformization t) : TateStructure W where
  t := t
  C := C
  hC := hC
  iso := (U.iso.trans (pointCongr hC).symm).trans (vcEquiv C W).symm
  iso_x u hu := by
    simp only [AddEquiv.trans_apply]
    rw [xCoord_eq_ptX, vcEquiv_symm_apply, ptX_pointCongr_symm]
    exact U.iso_x u hu
  iso_y u hu := by
    simp only [AddEquiv.trans_apply]
    rw [yCoord_eq_ptY, vcEquiv_symm_apply, ptY_pointCongr_symm]
    exact U.iso_y u hu

end Transport

section Torsion

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} {w : FinitePlace ↥K}

/-- Construct the Tate model at a bad place from the discriminant square root. -/
private theorem exists_tate_model_at_bad_place
    (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    (hw : IsBadPlace E K VBad w)
    (hSplitSquare : ∃ s : localCompletion w,
      s ^ 2 = emb K w (algebraMap F ↥K (-(E.c₄ * E.c₆)))) :
    ∃ (t : TateParameter (localCompletion w)) (D : VariableChange (localCompletion w)),
      D • curveKw E K w = t.tateCurve := by
  let v₀ : FinitePlace F := Tripod.placeUnder w
  have hmult₀ : HasMultiplicativeReductionAt E v₀ := mult_placeUnder E K hmult hw
  let C := (exists_variableChange_of_mult E v₀ hmult₀).choose
  have hC := (exists_variableChange_of_mult E v₀ hmult₀).choose_spec
  let Cw := (C.map (algebraMap F ↥K)).map (emb K w)
  have hCw : Cw • curveKw E K w = curveKw (C • E) K w :=
    (curveKw_variableChange E K C w).symm
  have hwv₀ : FinitePlace.LiesOver w v₀ := Tripod.liesOver_placeUnder w
  have hc₄ := norm_c₄_curveKw (C • E) K hwv₀ hC.2.1
  have hΔ := norm_Δ_curveKw (C • E) K hwv₀ hC.2.2
  have h2 := norm_two_curveKw E K hVBad hw
  have h12 := twelve_ne_zero w
  have h20 : (2 : localCompletion w) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact zero_ne_one h2
  have hc₄0 : (curveKw (C • E) K w).c₄ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc₄
    exact zero_ne_one hc₄
  have hsq : ∃ s : localCompletion w,
      s ^ 2 = -((curveKw E K w).c₄ * (curveKw E K w).c₆) := by
    rw [neg_c₄_mul_c₆_curveKw]
    exact hSplitSquare
  have hsqC := sq_neg_c₄_mul_c₆_variableChange (curveKw E K w) Cw hsq.choose_spec
  rw [hCw] at hsqC
  have hroot := exists_tangent_root_of_sq (curveKw (C • E) K w) h20 hc₄0 hsqC
  obtain ⟨t, D, hD, -⟩ :=
    exists_variableChange_tateCurve h2 h12 (curveKw (C • E) K w) hc₄ hΔ hroot
  refine ⟨t, D * Cw, ?_⟩
  rw [mul_smul, hCw, hD]

/-- Transport the uniformization of the selected Tate parameter to the original curve. -/
def tateStructureOfBadPlace
    (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    (hw : IsBadPlace E K VBad w)
    (hSplitSquare : ∃ s : localCompletion w,
      s ^ 2 = emb K w (algebraMap F ↥K (-(E.c₄ * E.c₆))))
    (uniformize : ∀ t : TateParameter (localCompletion w),
      (12 : localCompletion w) ≠ 0 → ‖(2 : localCompletion w)‖ = 1 →
      TateParameterUniformization t) :
    TateStructure (curveKw E K w) := by
  let model := exists_tate_model_at_bad_place E K hVBad hmult hw hSplitSquare
  let t := model.choose
  let C := model.choose_spec.choose
  exact TateStructure.ofVariableChangeWithUniformization t C model.choose_spec.choose_spec
    (uniformize t (twelve_ne_zero w) (norm_two_curveKw E K hVBad hw))

end Torsion

end

end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- Every finite place of the base field has a finite place above it. -/
theorem FinitePlace.exists_liesOver (v : FinitePlace k) :
    ∃ w : FinitePlace K, FinitePlace.LiesOver w v := by
  haveI : v.maximalIdeal.asIdeal.IsPrime := v.maximalIdeal.isPrime
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K)
    v.maximalIdeal.asIdeal ⊥ (by
      simpa only [Ideal.under_bot] using
        (bot_le : (⊥ : Ideal (𝓞 k)) ≤ v.maximalIdeal.asIdeal))
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    change (⊥ : Ideal (𝓞 K)).under (𝓞 k) = v.maximalIdeal.asIdeal at hQv
    rw [Ideal.under_bot] at hQv
    exact v.maximalIdeal.ne_bot hQv.symm
  refine ⟨FinitePlace.mk ⟨Q, hQ, hQne⟩, ?_⟩
  unfold FinitePlace.LiesOver
  rw [FinitePlace.maximalIdeal_mk]
  exact ⟨hQv.symm⟩

end AbcAdaptation.Reference.Iut

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/QuadraticExtension.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `e4777b2238f45be2e58c00b4d0213c0cb83405b9`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: copied into the JoshiTeich reference namespace; imports are adapted to local modules
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# Quadratic extensions `K(√d)` inside `F̄`

For a number field `K ⊆ F̄` (an intermediate field of an algebraic closure `F̄` of `F`) and
`d ∈ K`, the field `K(√d) ⊆ F̄` obtained by adjoining a chosen square root of `d` in `F̄`:

* `AbcAdaptation.Reference.Iut.sqrtField K d : IntermediateField ↥K Fbar` — the field `K(√d)`, a number field
  (`AbcAdaptation.Reference.Iut.instNumberFieldSqrtField`), of degree `≤ 2` over `K` (`AbcAdaptation.Reference.Iut.sqrtField_finrank_le`);
* `AbcAdaptation.Reference.Iut.sqrtD K d : ↥(sqrtField K d)` — the chosen square root, `AbcAdaptation.Reference.Iut.sqrtD_sq`;
* `AbcAdaptation.Reference.Iut.conj K d hd : K(√d) ≃ₐ[K] K(√d)` — for `d` **not a square** in `K`, the conjugation
  `√d ↦ -√d` (`AbcAdaptation.Reference.Iut.conj_sqrtD`), an involution (`AbcAdaptation.Reference.Iut.conj_conj`) fixing exactly `K`
  (`AbcAdaptation.Reference.Iut.eq_algebraMap_of_conj_eq`);
* `AbcAdaptation.Reference.Iut.exists_sq_eq_of_isSquare` — the trivial case `d` a square in `K`.
-/

namespace AbcAdaptation.Reference.Iut

open NumberField Polynomial

variable {F : Type*} [Field F]
variable {Fbar : Type*} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar)

/-! ### The polynomial `X² − d` -/

/-- The polynomial `X² − d` over `K`. -/
noncomputable abbrev sqrtPoly (d : ↥K) : (↥K)[X] := X ^ 2 - C d

lemma sqrtPoly_monic (d : ↥K) : (sqrtPoly K d).Monic := monic_X_pow_sub_C d two_ne_zero

lemma sqrtPoly_natDegree (d : ↥K) : (sqrtPoly K d).natDegree = 2 := natDegree_X_pow_sub_C

lemma sqrtPoly_ne_zero (d : ↥K) : sqrtPoly K d ≠ 0 := X_pow_sub_C_ne_zero two_pos d

/-- The trivial case: if `d` is a square in `K` then it has a square root in `K`. -/
theorem exists_sq_eq_of_isSquare {d : ↥K} (hd : IsSquare d) : ∃ y : ↥K, y ^ 2 = d := by
  obtain ⟨r, hr⟩ := hd
  exact ⟨r, by rw [sq, hr]⟩

/-- `X² − d` is irreducible over `K` when `d` is not a square in `K`. -/
theorem sqrtPoly_irreducible {d : ↥K} (hd : ¬ IsSquare d) : Irreducible (sqrtPoly K d) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [sqrtPoly_natDegree]; decide
  · intro x hx
    apply hd
    refine ⟨x, ?_⟩
    have : x ^ 2 - d = 0 := by simpa [sqrtPoly] using hx
    rw [← sq, eq_comm, ← sub_eq_zero]
    exact this

/-! ### The chosen square root and the field `K(√d)` -/

variable [IsAlgClosure F Fbar]

/-- A chosen square root in `F̄` of `d ∈ K`. -/
noncomputable def sqrtRoot (d : ↥K) : Fbar :=
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Fbar d) two_pos)

lemma sqrtRoot_sq (d : ↥K) : sqrtRoot K d ^ 2 = algebraMap ↥K Fbar d :=
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Fbar d) two_pos)

lemma aeval_sqrtRoot (d : ↥K) : aeval (sqrtRoot K d) (sqrtPoly K d) = 0 := by
  simp [sqrtPoly, sqrtRoot_sq]

lemma sqrtRoot_isIntegral (d : ↥K) : IsIntegral ↥K (sqrtRoot K d) :=
  ⟨sqrtPoly K d, sqrtPoly_monic K d, by simpa [aeval_def] using aeval_sqrtRoot K d⟩

lemma minpoly_sqrtRoot_dvd (d : ↥K) : minpoly ↥K (sqrtRoot K d) ∣ sqrtPoly K d :=
  minpoly.dvd _ _ (aeval_sqrtRoot K d)

/-- The field `K(√d) ⊆ F̄`, generated over `K` by the chosen square root of `d`. -/
noncomputable def sqrtField (d : ↥K) : IntermediateField ↥K Fbar :=
  IntermediateField.adjoin ↥K {sqrtRoot K d}

instance (d : ↥K) : FiniteDimensional ↥K ↥(sqrtField K d) :=
  IntermediateField.adjoin.finiteDimensional (sqrtRoot_isIntegral K d)

/-- The chosen square root of `d`, as an element of `K(√d)`. -/
noncomputable def sqrtD (d : ↥K) : ↥(sqrtField K d) :=
  ⟨sqrtRoot K d, IntermediateField.mem_adjoin_simple_self ↥K (sqrtRoot K d)⟩

@[simp] lemma coe_sqrtD (d : ↥K) : (sqrtD K d : Fbar) = sqrtRoot K d := rfl

lemma sqrtD_eq_gen (d : ↥K) :
    sqrtD K d = IntermediateField.AdjoinSimple.gen ↥K (sqrtRoot K d) := rfl

/-- `√d ^ 2 = d` in `K(√d)`. -/
theorem sqrtD_sq (d : ↥K) : sqrtD K d ^ 2 = algebraMap ↥K ↥(sqrtField K d) d := by
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, coe_sqrtD, sqrtRoot_sq]
  rfl

/-- `[K(√d) : K] ≤ 2`. -/
theorem sqrtField_finrank_le (d : ↥K) : Module.finrank ↥K ↥(sqrtField K d) ≤ 2 := by
  rw [sqrtField, IntermediateField.adjoin.finrank (sqrtRoot_isIntegral K d)]
  calc (minpoly ↥K (sqrtRoot K d)).natDegree ≤ (sqrtPoly K d).natDegree :=
        natDegree_le_of_dvd (minpoly_sqrtRoot_dvd K d) (sqrtPoly_ne_zero K d)
    _ = 2 := sqrtPoly_natDegree K d

/-! ### The conjugation `√d ↦ -√d` when `d` is not a square -/

/-- `X² − d` is the minimal polynomial of `√d` over `K` when `d` is not a square in `K`. -/
theorem minpoly_sqrtRoot {d : ↥K} (hd : ¬ IsSquare d) :
    minpoly ↥K (sqrtRoot K d) = sqrtPoly K d :=
  (minpoly.eq_of_irreducible_of_monic (sqrtPoly_irreducible K hd) (aeval_sqrtRoot K d)
    (sqrtPoly_monic K d)).symm

/-- The power basis `{1, √d}` of `K(√d)` over `K`. -/
noncomputable def sqrtPowerBasis (d : ↥K) : PowerBasis ↥K ↥(sqrtField K d) :=
  IntermediateField.adjoin.powerBasis (sqrtRoot_isIntegral K d)

lemma sqrtPowerBasis_gen (d : ↥K) : (sqrtPowerBasis K d).gen = sqrtD K d := rfl

lemma minpoly_sqrtD {d : ↥K} (hd : ¬ IsSquare d) :
    minpoly ↥K (sqrtD K d) = sqrtPoly K d := by
  have h := IntermediateField.minpoly_gen (F := ↥K) (sqrtRoot K d)
  rw [minpoly_sqrtRoot K hd] at h
  exact h

lemma aeval_neg_sqrtD (d : ↥K) : aeval (-sqrtD K d) (sqrtPoly K d) = 0 := by
  simp [sqrtPoly, sqrtD_sq]

/-- The conjugation `√d ↦ -√d` as a `K`-algebra endomorphism of `K(√d)`. -/
noncomputable def conjHom {d : ↥K} (hd : ¬ IsSquare d) :
    ↥(sqrtField K d) →ₐ[↥K] ↥(sqrtField K d) :=
  (sqrtPowerBasis K d).lift (-sqrtD K d) (by
    rw [sqrtPowerBasis_gen, minpoly_sqrtD K hd]
    exact aeval_neg_sqrtD K d)

lemma conjHom_sqrtD {d : ↥K} (hd : ¬ IsSquare d) : conjHom K hd (sqrtD K d) = -sqrtD K d :=
  (sqrtPowerBasis K d).lift_gen _ _

lemma conjHom_comp_conjHom {d : ↥K} (hd : ¬ IsSquare d) :
    (conjHom K hd).comp (conjHom K hd) = AlgHom.id ↥K ↥(sqrtField K d) :=
  (sqrtPowerBasis K d).algHom_ext (by
    rw [sqrtPowerBasis_gen, AlgHom.comp_apply, conjHom_sqrtD, map_neg, conjHom_sqrtD, neg_neg,
      AlgHom.id_apply])

/-- **The conjugation** `√d ↦ -√d` of `K(√d)` over `K`, for `d` not a square in `K`. -/
noncomputable def conj {d : ↥K} (hd : ¬ IsSquare d) :
    ↥(sqrtField K d) ≃ₐ[↥K] ↥(sqrtField K d) :=
  AlgEquiv.ofAlgHom (conjHom K hd) (conjHom K hd) (conjHom_comp_conjHom K hd)
    (conjHom_comp_conjHom K hd)

/-- The conjugation sends `√d` to `-√d`. -/
@[simp] theorem conj_sqrtD {d : ↥K} (hd : ¬ IsSquare d) : conj K hd (sqrtD K d) = -sqrtD K d :=
  conjHom_sqrtD K hd

/-! ### `K(√d)` as a number field -/

variable [NumberField ↥K]

instance (d : ↥K) : NumberField ↥(sqrtField K d) :=
  NumberField.of_module_finite ↥K ↥(sqrtField K d)

end AbcAdaptation.Reference.Iut

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/ValuationTransfer.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `e4777b2238f45be2e58c00b4d0213c0cb83405b9`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: Mathlib compatibility adaptation in the JoshiTeich reference port
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# Valuation transfer along places of an extension

For number fields `k ⊆ K` and finite places `w | v` (`AbcAdaptation.Reference.Iut.FinitePlace.LiesOver w v`):

* **valuation transfer**: the `w`-adic valuation of `algebraMap k K x` is the `e`-th power
  of the `v`-adic valuation of `x` (Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`), so the conditions `≤ 1`, `< 1`,
  `= 1` transfer (`AbcAdaptation.Reference.Iut.valuation_algebraMap_le_one_iff`, …), also for the norms on the
  completions (`AbcAdaptation.Reference.Iut.norm_emb_algebraMap_le_one_iff`, …);
* **integral approximation**: an element of `K` which is `w`-integral is congruent modulo
  the maximal ideal to an element of `𝓞_K` (`AbcAdaptation.Reference.Iut.exists_ringOfIntegers_sub_mem`);
* **residue degree one**: if `f(w/v) = 1`, the residue map `𝓞_k/v → 𝓞_K/w` is surjective
  (`AbcAdaptation.Reference.Iut.exists_algebraMap_sub_mem_of_inertiaDeg_eq_one`);
* **two places above `v` in a quadratic extension** have `e = f = 1`
  (`AbcAdaptation.Reference.Iut.inertiaDeg'_eq_one_of_ne`, `AbcAdaptation.Reference.Iut.ramificationIdx'_eq_one_of_ne`), from the fundamental
  identity `∑ e f = [K : k]`.
-/

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ## Valuation transfer -/

section Norm

variable {w : FinitePlace K}

lemma norm_emb_lt_one_iff (y : K) :
    ‖(FinitePlace.embedding w.maximalIdeal y : localCompletion w)‖ < 1 ↔
      w.maximalIdeal.valuation K y < 1 := by
  rw [norm_lt_one_iff_valued, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

lemma norm_emb_eq_one_iff (y : K) :
    ‖(FinitePlace.embedding w.maximalIdeal y : localCompletion w)‖ = 1 ↔
      w.maximalIdeal.valuation K y = 1 := by
  rw [norm_eq_one_iff_valued, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

end Norm

section Transfer

variable {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)
include hwv

lemma valuation_algebraMap_lt_one_iff (x : k) :
    w.maximalIdeal.valuation K (algebraMap k K x) < 1 ↔ v.maximalIdeal.valuation k x < 1 := by
  rw [Tripod.valuation_algebraMap_eq_pow hwv]
  exact pow_lt_one_iff_of_nonneg zero_le (Tripod.ramificationIdx'_ne_zero hwv)

lemma valuation_algebraMap_eq_one_iff (x : k) :
    w.maximalIdeal.valuation K (algebraMap k K x) = 1 ↔ v.maximalIdeal.valuation k x = 1 := by
  rw [Tripod.valuation_algebraMap_eq_pow hwv]
  exact pow_eq_one_iff_of_nonneg zero_le (Tripod.ramificationIdx'_ne_zero hwv)

end Transfer

/-! ## Integral approximation -/

section Approx

variable (w : FinitePlace K)

/-- An element `x ∈ K` with `w(x) ≤ 1` is congruent modulo the maximal ideal to an element of
`𝓞_K`: there is `a ∈ 𝓞_K` with `w(x - a) < 1`. -/
lemma exists_ringOfIntegers_sub_mem (x : K) (hx : w.maximalIdeal.valuation K x ≤ 1) :
    ∃ a : 𝓞 K, w.maximalIdeal.valuation K (x - algebraMap (𝓞 K) K a) < 1 := by
  set P := w.maximalIdeal with hP
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 K) K b ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact hb0
  have hvb : 0 < P.intValuation b := by
    rw [pos_iff_ne_zero]
    exact P.intValuation_ne_zero b hb0
  -- the `w`-adic order `m` of the denominator
  set m : ℕ := multiplicity P.asIdeal (Ideal.span {b}) with hm
  have hbm : P.intValuation b = WithZero.exp (-(m : ℤ)) :=
    intValuation_eq_exp_neg_multiplicity P hb0
  have hb_mem : b ∈ P.asIdeal ^ m := by
    rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd, hbm]
  have hb_notMem : b ∉ P.asIdeal ^ (m + 1) := by
    rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd, hbm, WithZero.exp_le_exp]
    omega
  have ha_mem : a ∈ P.asIdeal ^ m := by
    rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd, ← hbm]
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap, div_le_one₀ hvb] at hx
    exact hx
  obtain ⟨d, e, he, hde⟩ :=
    Ideal.exists_mul_add_mem_pow_succ P.ne_bot b a hb_mem hb_notMem ha_mem
  refine ⟨d, ?_⟩
  have hxd : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b - algebraMap (𝓞 K) K d =
      algebraMap (𝓞 K) K e / algebraMap (𝓞 K) K b := by
    rw [eq_div_iff hb', sub_mul, div_mul_cancel₀ _ hb', ← hde, map_add, map_mul]
    ring
  rw [hxd, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap, div_lt_one₀ hvb, hbm]
  refine lt_of_le_of_lt ((intValuation_le_pow_iff_dvd P e (m + 1)).2
    (Ideal.dvd_span_singleton.2 he)) ?_
  rw [WithZero.exp_lt_exp]
  omega

end Approx

/-! ## Residue degree one -/

section Residue

variable {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)
include hwv

/-- If the residue degree of `w` over `v` is `1`, the residue map `𝓞_k/v → 𝓞_K/w` is
surjective: every `a ∈ 𝓞_K` is congruent modulo `w` to an element of `𝓞_k`. -/
lemma exists_algebraMap_sub_mem_of_inertiaDeg_eq_one
    (hf : v.maximalIdeal.asIdeal.inertiaDeg' w.maximalIdeal.asIdeal = 1) (a : 𝓞 K) :
    ∃ b : 𝓞 k, algebraMap (𝓞 k) (𝓞 K) b - a ∈ w.maximalIdeal.asIdeal := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ v.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 K ⧸ w.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  rw [Ideal.inertiaDeg'_algebraMap,
    finrank_eq_one_iff_of_nonzero' (1 : 𝓞 K ⧸ w.maximalIdeal.asIdeal) one_ne_zero] at hf
  obtain ⟨c, hc⟩ := hf (Ideal.Quotient.mk _ a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨b, ?_⟩
  rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_mk_of_liesOver] at hc
  exact Ideal.Quotient.eq.1 hc

end Residue

/-! ## Two places above a place in a quadratic extension -/

section Quadratic

variable {v : FinitePlace k}

/-- If `[K : k] ≤ 2` and two distinct places `w₁ ≠ w₂` of `K` lie over `v`, then
`e(w₁/v) f(w₁/v) = 1`. -/
lemma ramificationIdx'_mul_inertiaDeg'_eq_one_of_ne (hK : Module.finrank k K ≤ 2)
    {w₁ w₂ : FinitePlace K} (hne : w₁ ≠ w₂) (h₁ : FinitePlace.LiesOver w₁ v)
    (h₂ : FinitePlace.LiesOver w₂ v) :
    v.maximalIdeal.asIdeal.ramificationIdx' w₁.maximalIdeal.asIdeal *
      v.maximalIdeal.asIdeal.inertiaDeg' w₁.maximalIdeal.asIdeal = 1 := by
  classical
  haveI : w₁.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := h₁
  haveI : w₂.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := h₂
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  have hp0 : v.maximalIdeal.asIdeal ≠ ⊥ := v.maximalIdeal.ne_bot
  have hsum := Ideal.sum_ramification_inertia (𝓞 K) k K hp0 (p := v.maximalIdeal.asIdeal)
  have hmem₁ : w₁.maximalIdeal.asIdeal ∈ IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨inferInstance, h₁⟩
  have hmem₂ : w₂.maximalIdeal.asIdeal ∈ IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨inferInstance, h₂⟩
  have hne' : w₁.maximalIdeal.asIdeal ≠ w₂.maximalIdeal.asIdeal := fun h =>
    hne ((FinitePlace.maximalIdeal_inj _ _).mp (HeightOneSpectrum.ext h))
  have hsub : ({w₁.maximalIdeal.asIdeal, w₂.maximalIdeal.asIdeal} : Finset (Ideal (𝓞 K))) ⊆
      IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 K) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hmem₁
    · exact hmem₂
  have hle := Finset.sum_le_sum_of_subset (f := fun P : Ideal (𝓞 K) =>
    v.maximalIdeal.asIdeal.ramificationIdx' P * v.maximalIdeal.asIdeal.inertiaDeg' P) hsub
  rw [Finset.sum_pair hne', hsum] at hle
  have he₁ : 0 < v.maximalIdeal.asIdeal.ramificationIdx' w₁.maximalIdeal.asIdeal :=
    Nat.pos_of_ne_zero (Tripod.ramificationIdx'_ne_zero h₁)
  have he₂ : 0 < v.maximalIdeal.asIdeal.ramificationIdx' w₂.maximalIdeal.asIdeal :=
    Nat.pos_of_ne_zero (Tripod.ramificationIdx'_ne_zero h₂)
  have hf₁ : 0 < v.maximalIdeal.asIdeal.inertiaDeg' w₁.maximalIdeal.asIdeal :=
    Ideal.inertiaDeg'_pos _ _
  have hf₂ : 0 < v.maximalIdeal.asIdeal.inertiaDeg' w₂.maximalIdeal.asIdeal :=
    Ideal.inertiaDeg'_pos _ _
  have h1 := Nat.mul_pos he₁ hf₁
  have h2 := Nat.mul_pos he₂ hf₂
  omega

/-- If `[K : k] ≤ 2` and two distinct places of `K` lie over `v`, then the residue degree of
each is `1`. -/
lemma inertiaDeg'_eq_one_of_ne (hK : Module.finrank k K ≤ 2)
    {w₁ w₂ : FinitePlace K} (hne : w₁ ≠ w₂) (h₁ : FinitePlace.LiesOver w₁ v)
    (h₂ : FinitePlace.LiesOver w₂ v) :
    v.maximalIdeal.asIdeal.inertiaDeg' w₁.maximalIdeal.asIdeal = 1 :=
  Nat.eq_one_of_mul_eq_one_left (ramificationIdx'_mul_inertiaDeg'_eq_one_of_ne hK hne h₁ h₂)

end Quadratic

end AbcAdaptation.Reference.Iut

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Adapted from Iut/Cor312/ThetaData/PointMap.lean and TateFamilyGalois.lean
at lana-agents/iut, revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
-/
namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve

section PointMap

variable {k K : Type*} [Field k] [Field K]
variable (E : WeierstrassCurve k) (f : k →+* K)

lemma pointMap_some {x y : k} (h : E.toAffine.Nonsingular x y) :
    pointMap E f (Affine.Point.some x y h) =
      Affine.Point.some (f x) (f y) ((E.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

lemma pointMap_injective : Function.Injective (pointMap E f) := by
  classical
  letI := f.toAlgebra
  exact Affine.Point.map_injective (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

end PointMap

end AbcAdaptation.Reference.Iut.Anabelian

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve Anabelian

variable {k : Type*} [Field k]

lemma pointCongr_some {W W' : WeierstrassCurve k} (h : W = W') {x y : k}
    (hxy : W.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst h
  rfl

end AbcAdaptation.Reference.Iut

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/GalCompletion.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: Mathlib compatibility adaptation in the JoshiTeich reference port
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# The Galois action on the completions at finite places

For number fields `k ⊆ K`, `σ ∈ Gal(K/k)` and a finite place `w` of `K`, the automorphism `σ`
carries the `w`-adic valuation to the `σ·w`-adic valuation
(`AbcAdaptation.Reference.Iut.galPlace_valuation`), hence extends to an isomorphism of the completions
`σ_w : K_w ≃+* K_{σ·w}` (`AbcAdaptation.Reference.Iut.galCompletion σ w`) which is continuous with continuous inverse,
extends `σ` (`AbcAdaptation.Reference.Iut.galCompletion_emb`), preserves the valuation
(`AbcAdaptation.Reference.Iut.valued_galCompletion`) and the norm (`AbcAdaptation.Reference.Iut.norm_galCompletion`).

The construction is done in two general layers:

* `AbcAdaptation.Reference.Iut.ValuedHom`: a ring homomorphism `φ : K → K` with `v' ∘ φ = v` between two valuations on a
  field is uniformly continuous for the valuation uniformities, so extends to a continuous ring
  homomorphism `AbcAdaptation.Reference.Iut.completionMap : v.Completion →+* v'.Completion` preserving the valuation;
* `AbcAdaptation.Reference.Iut.adicCompletionMap`: the same for the adic completions of a Dedekind domain at two height-one
  primes, together with an extensionality principle for continuous ring homomorphisms out of an
  adic completion (`AbcAdaptation.Reference.Iut.adicCompletion_hom_ext`).

The input `AbcAdaptation.Reference.Iut.galPlace_valuation` is obtained from the general transport of `intValuation` and
`valuation` along a ring isomorphism of Dedekind domains (`AbcAdaptation.Reference.Iut.intValuation_of_comap`,
`AbcAdaptation.Reference.Iut.valuation_of_comap`). The file also records `AbcAdaptation.Reference.Iut.galPlace_one` and
`AbcAdaptation.Reference.Iut.galPlace_inv_galPlace` (the action of `Gal(K/k)` on places is an action).
-/

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain WithZero

noncomputable section

/-! ### Valuation-preserving homomorphisms and completions -/

section ValuedHom

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v v' : Valuation K Γ₀) (φ : K →+* K)

/-- The valuation of `WithVal.map v v' φ x` for a valuation-preserving `φ`. -/
theorem valued_withValMap (hφ : ∀ x, v' (φ x) = v x) (x : WithVal v) :
    Valued.v (WithVal.map v v' φ x) = Valued.v x := by
  rw [WithVal.map_apply, WithVal.valued_toVal, hφ, WithVal.apply_ofVal]

/-- A valuation-preserving ring homomorphism is uniformly continuous (for `v` surjective). -/
theorem uniformContinuous_withValMap (hφ : ∀ x, v' (φ x) = v x)
    (hv : Function.Surjective v) : UniformContinuous (WithVal.map v v' φ) := by
  refine uniformContinuous_of_continuousAt_zero (WithVal.map v v' φ) ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨x₀, hx₀⟩ := hv (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hne : (Valued.v : Valuation (WithVal v) Γ₀).restrict (WithVal.toVal v x₀) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, WithVal.valued_toVal, hx₀]
    exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hne, fun x hx => hγ ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff, WithVal.valued_toVal,
    hx₀] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding,
    valued_withValMap v v' φ hφ]
  exact hx

/-- The continuous ring homomorphism of completions induced by a valuation-preserving `φ`. -/
def completionMap (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v) :
    v.Completion →+* v'.Completion :=
  UniformSpace.Completion.mapRingHom (WithVal.map v v' φ)
    (uniformContinuous_withValMap v v' φ hφ hv).continuous

variable {v v' φ}

theorem continuous_completionMap (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v) :
    Continuous (completionMap v v' φ hφ hv) :=
  UniformSpace.Completion.continuous_map

theorem completionMap_coe' (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v)
    (x : WithVal v) :
    completionMap v v' φ hφ hv (x : v.Completion) = (WithVal.map v v' φ x : v'.Completion) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem completionMap_coe (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v) (x : K) :
    completionMap v v' φ hφ hv (x : v.Completion) = (φ x : v'.Completion) :=
  completionMap_coe' hφ hv _

/-- The extension of a valuation-preserving homomorphism to the completions preserves the
valuation. -/
theorem valued_completionMap (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v)
    (y : v.Completion) : Valued.v (completionMap v v' φ hφ hv y) = Valued.v y := by
  by_cases hy : y = 0
  · subst hy; simp
  have hfy : completionMap v v' φ hφ hv y ≠ 0 := (map_ne_zero _).2 hy
  have h1 : {z | Valued.v z = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have h2 : (completionMap v v' φ hφ hv) ⁻¹'
      {z | Valued.v z = Valued.v (completionMap v v' φ hφ hv y)} ∈ nhds y :=
    (continuous_completionMap hφ hv).continuousAt.preimage_mem_nhds
      (Valued.locally_const ((Valuation.ne_zero_iff _).2 hfy))
  obtain ⟨t, hts, ht, hyt⟩ := mem_nhds_iff.1 (Filter.inter_mem h1 h2)
  obtain ⟨r, hr⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open ht ⟨y, hyt⟩
  obtain ⟨hr1, hr2⟩ := hts hr
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hr1 hr2
  rw [← hr1, ← hr2, completionMap_coe', Valued.valuedCompletion_apply,
    Valued.valuedCompletion_apply, valued_withValMap v v' φ hφ]

end ValuedHom

/-! ### Adic completions -/

section Adic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The image of `K` is dense in its `v`-adic completion. -/
theorem denseRange_coe_adicCompletion (v : HeightOneSpectrum R) :
    DenseRange ((↑) : K → v.adicCompletion K) := by
  have h : ((↑) : K → v.adicCompletion K) =
      HeightOneSpectrum.adicCompletion.ofCompletion ∘ ((↑) : WithVal (v.valuation K) → _) ∘
        (WithVal.equiv (v.valuation K)).symm := rfl
  rw [h]
  exact ((HeightOneSpectrum.adicCompletion.ofCompletion_surjective K v).denseRange.comp
    (UniformSpace.Completion.denseRange_coe.comp
      (WithVal.equiv (v.valuation K)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _))
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v))

/-- Continuous ring homomorphisms out of an adic completion are determined by their values on
`K`. -/
theorem adicCompletion_hom_ext (v : HeightOneSpectrum R) {A : Type*} [TopologicalSpace A]
    [T2Space A] [NonAssocSemiring A] {f g : v.adicCompletion K →+* A} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ x : K, f x = g x) : f = g :=
  RingHom.ext (congr_fun ((denseRange_coe_adicCompletion v).equalizer hf hg (funext h)))

variable (v v' : HeightOneSpectrum R) (φ : K →+* K)

/-- The continuous ring homomorphism `K_v → K_{v'}` induced by `φ : K → K` carrying the `v`-adic
valuation to the `v'`-adic valuation. -/
def adicCompletionMap (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x) :
    v.adicCompletion K →+* v'.adicCompletion K :=
  (HeightOneSpectrum.adicCompletion.equiv K v').symm.toRingHom.comp
    ((completionMap (v.valuation K) (v'.valuation K) φ hφ (v.valuation_surjective K)).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom)

variable {v v' φ}

theorem adicCompletionMap_coe (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x) (x : K) :
    adicCompletionMap v v' φ hφ (x : v.adicCompletion K) = (φ x : v'.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  exact completionMap_coe hφ (v.valuation_surjective K) x

theorem continuous_adicCompletionMap (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x) :
    Continuous (adicCompletionMap v v' φ hφ) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v').comp
    ((continuous_completionMap hφ (v.valuation_surjective K)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v))

theorem valued_adicCompletionMap (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x)
    (y : v.adicCompletion K) : Valued.v (adicCompletionMap v v' φ hφ y) = Valued.v y :=
  valued_completionMap hφ (v.valuation_surjective K) y.toCompletion

end Adic

/-! ### Valuations along ring isomorphisms of Dedekind domains -/

section IntValuation

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]

omit [IsDedekindDomain R] [IsDedekindDomain S] in
lemma mem_comap_pow_iff (f : R →+* S) (hf : Function.Bijective f) (I : Ideal S) (a : R)
    (n : ℕ) : a ∈ (I.comap f) ^ n ↔ f a ∈ I ^ n := by
  let e := RingEquiv.ofBijective f hf
  have he : I.comap f = I.comap e := by
    ext x; rw [Ideal.mem_comap, Ideal.mem_comap, RingEquiv.coe_ofBijective]
  have hea : f a = e a := (RingEquiv.coe_ofBijective f hf).symm ▸ rfl
  rw [he, hea, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]

/-- The `intValuation` at the prime `w = f⁻¹(v)` of `a` is the `intValuation` at `v` of `f a`. -/
theorem intValuation_of_comap {v : HeightOneSpectrum S} {w : HeightOneSpectrum R} (f : R →+* S)
    (hf : Function.Bijective f) (hw : w.asIdeal = v.asIdeal.comap f) (a : R) :
    w.intValuation a = v.intValuation (f a) := by
  have key : ∀ n : ℕ, w.intValuation a ≤ exp (-(n : ℤ)) ↔
      v.intValuation (f a) ≤ exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      hw]
    exact mem_comap_pow_iff f hf v.asIdeal a n
  by_cases ha : a = 0
  · subst ha; simp
  have hfa : f a ≠ 0 := (map_ne_zero_iff f hf.injective).2 ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, w.intValuation a = exp (-(m : ℤ)) :=
    ⟨_, w.intValuation_if_neg ha⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, v.intValuation (f a) = exp (-(m' : ℤ)) :=
    ⟨_, v.intValuation_if_neg hfa⟩
  rw [hm, hm'] at key ⊢
  simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at key
  rw [le_antisymm ((key m).1 le_rfl) ((key m').2 le_rfl)]

/-- The valuation at `w = f⁻¹(v)` of `x` is the valuation at `v` of `φ x`, for `φ` a field
homomorphism extending `f`. -/
theorem valuation_of_comap {K L : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra S L] [IsFractionRing S L] {v : HeightOneSpectrum S} {w : HeightOneSpectrum R}
    (f : R →+* S) (hf : Function.Bijective f) (hw : w.asIdeal = v.asIdeal.comap f)
    (φ : K →+* L) (hφ : ∀ r : R, φ (algebraMap R K r) = algebraMap S L (f r)) (x : K) :
    w.valuation K x = v.valuation L (φ x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have h3 : v.valuation L (algebraMap S L (f r)) = v.intValuation (f r) :=
    v.valuation_of_algebraMap (K := L) (f r)
  have h4 : v.valuation L (algebraMap S L (f s)) = v.intValuation (f s) :=
    v.valuation_of_algebraMap (K := L) (f s)
  change w.valuation K (IsLocalization.mk' K r s) = v.valuation L (φ (IsLocalization.mk' K r s))
  rw [HeightOneSpectrum.valuation_of_mk', IsFractionRing.mk'_eq_div, map_div₀, hφ, hφ, map_div₀,
    h3, h4, intValuation_of_comap f hf hw, intValuation_of_comap f hf hw]

end IntValuation

/-! ### The Galois action on valuations and completions -/

section Galois

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

lemma galRestrictInt_bijective (σ : K ≃ₐ[k] K) :
    Function.Bijective (galRestrictInt σ : 𝓞 K →+* 𝓞 K) :=
  (galRestrictInt σ).bijective

lemma algebraMap_galRestrictInt (σ : K ≃ₐ[k] K) (r : 𝓞 K) :
    (σ : K →+* K) (algebraMap (𝓞 K) K r) =
      algebraMap (𝓞 K) K ((galRestrictInt σ : 𝓞 K →+* 𝓞 K) r) :=
  (coe_galRestrictInt σ r).symm

/-- **`σ⁻¹` carries the `σ·w`-adic valuation to the `w`-adic valuation.** -/
theorem galPlace_valuation_inv (σ : K ≃ₐ[k] K) (w : FinitePlace K) (x : K) :
    w.maximalIdeal.valuation K (σ⁻¹ x) = (galPlace σ w).maximalIdeal.valuation K x := by
  have h := valuation_of_comap (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K)
    (galRestrictInt_bijective σ⁻¹) (galPlace_maximalIdeal σ w)
    ((σ⁻¹ : K ≃ₐ[k] K) : K →+* K) (algebraMap_galRestrictInt σ⁻¹) x
  rw [RingHom.coe_coe] at h
  exact h.symm

/-- **`σ` carries the `w`-adic valuation to the `σ·w`-adic valuation.** -/
theorem galPlace_valuation (σ : K ≃ₐ[k] K) (w : FinitePlace K) (x : K) :
    (galPlace σ w).maximalIdeal.valuation K (σ x) = w.maximalIdeal.valuation K x := by
  rw [← galPlace_valuation_inv σ w (σ x), AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

/-- **The absolute norm of the prime of `σ·w` is that of the prime of `w`.** -/
theorem absNorm_galPlace (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    Ideal.absNorm (galPlace σ w).maximalIdeal.asIdeal = Ideal.absNorm w.maximalIdeal.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  let e : 𝓞 K ≃+* 𝓞 K := (galRestrictInt σ⁻¹).toRingEquiv
  have hIJ : w.maximalIdeal.asIdeal = (galPlace σ w).maximalIdeal.asIdeal.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [galPlace_maximalIdeal]
    have : (e : 𝓞 K →+* 𝓞 K) = (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K) := RingHom.ext fun _ => rfl
    rw [this, Ideal.map_comap_of_surjective (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K)
      (galRestrictInt_bijective σ⁻¹).surjective]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ e hIJ).toEquiv

/-- **The isomorphism of completions `K_w ≃ K_{σ·w}` induced by `σ ∈ Gal(K/k)`.** -/
def galCompletion (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    localCompletion w ≃+* localCompletion (galPlace σ w) :=
  RingEquiv.ofRingHom
    (adicCompletionMap w.maximalIdeal (galPlace σ w).maximalIdeal (σ : K →+* K)
      (by
        intro x
        rw [RingHom.coe_coe]
        exact galPlace_valuation σ w x))
    (adicCompletionMap (galPlace σ w).maximalIdeal w.maximalIdeal
      ((σ⁻¹ : K ≃ₐ[k] K) : K →+* K)
      (by
        intro x
        rw [RingHom.coe_coe]
        exact galPlace_valuation_inv σ w x))
    (adicCompletion_hom_ext _
      ((continuous_adicCompletionMap _).comp (continuous_adicCompletionMap _)) continuous_id
      (fun x => by
        rw [RingHom.comp_apply, adicCompletionMap_coe, adicCompletionMap_coe, RingHom.id_apply]
        simp))
    (adicCompletion_hom_ext _
      ((continuous_adicCompletionMap _).comp (continuous_adicCompletionMap _)) continuous_id
      (fun x => by
        rw [RingHom.comp_apply, adicCompletionMap_coe, adicCompletionMap_coe, RingHom.id_apply]
        simp))

variable (σ : K ≃ₐ[k] K) (w : FinitePlace K)

/-- `σ_w` extends `σ`. -/
theorem galCompletion_embedding (x : K) :
    galCompletion σ w (FinitePlace.embedding w.maximalIdeal x) =
      FinitePlace.embedding (galPlace σ w).maximalIdeal (σ x) :=
  adicCompletionMap_coe _ x

/-- **`σ_w` preserves the valuation.** -/
theorem valued_galCompletion (x : localCompletion w) :
    Valued.v (galCompletion σ w x) = Valued.v x :=
  valued_adicCompletionMap _ x

lemma toNNReal_congr {e e' : NNReal} (h : e = e') (he : e ≠ 0) (he' : e' ≠ 0) (x : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal he x = WithZeroMulInt.toNNReal he' x := by
  subst h; rfl

/-- **`σ_w` is an isometry** for the normed-field structures of the completions. -/
theorem norm_galCompletion (x : localCompletion w) : ‖galCompletion σ w x‖ = ‖x‖ := by
  rw [FinitePlace.norm_def, FinitePlace.norm_def, valued_galCompletion]
  congr 1
  exact toNNReal_congr (by rw [absNorm_galPlace]) _ _ _

end Galois

end

end AbcAdaptation.Reference.Iut

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/LocalAut.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `e4777b2238f45be2e58c00b4d0213c0cb83405b9`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: Mathlib compatibility adaptation in the JoshiTeich reference port
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# The local automorphism at a Galois-fixed place, and the curve over the completion

For a Galois automorphism `σ ∈ Gal(K'/k)` fixing a finite place `w` of `K'`, the isometry
`K'_w ≃ K'_{σw}` of `AbcAdaptation.Reference.Iut.galCompletion` becomes an automorphism `AbcAdaptation.Reference.Iut.localAut σ w hfix` of
`K'_w` extending `σ`. For an elliptic curve `E` over a subfield `F` of `k`, the curve
`AbcAdaptation.Reference.Iut.curveLoc E K' w = E ×_F K'_w` is fixed by this automorphism, and the points of `E(k)`
map to fixed points of `E(K'_w)`.
-/

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve AbcAdaptation.Reference.Iut.Anabelian
open scoped Classical Valued

universe u

noncomputable section

section Cast

variable {k : Type*} [Field k] [NumberField k]

/-- Transport along an equality of places. -/
def placeCast {w₁ w₂ : FinitePlace k} (h : w₁ = w₂) :
    localCompletion w₁ ≃+* localCompletion w₂ := by
  subst h
  exact RingEquiv.refl _

@[simp] lemma norm_placeCast {w₁ w₂ : FinitePlace k} (h : w₁ = w₂) (x : localCompletion w₁) :
    ‖placeCast h x‖ = ‖x‖ := by
  subst h
  rfl

lemma placeCast_embedding {w₁ w₂ : FinitePlace k} (h : w₁ = w₂) (x : k) :
    placeCast h (FinitePlace.embedding w₁.maximalIdeal x) =
      FinitePlace.embedding w₂.maximalIdeal x := by
  subst h
  rfl

end Cast

section LocalCurve

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F)
variable (K' : Type u) [Field K'] [NumberField K'] [Algebra F K'] (w : FinitePlace K')

/-- `E` over the completion `K'_w` of a number field `K' ⊇ F`. -/
abbrev curveLoc : WeierstrassCurve (localCompletion w) :=
  (E.map (algebraMap F K')).map (FinitePlace.embedding w.maximalIdeal)

end LocalCurve

section Aut

variable {k : Type u} [Field k] [NumberField k] {K' : Type u} [Field K'] [NumberField K']
  [Algebra k K'] (σ : K' ≃ₐ[k] K') (w : FinitePlace K') (hfix : galPlace σ w = w)

/-- The automorphism of `K'_w` extending `σ`, at a place fixed by `σ`. -/
def localAut : localCompletion w ≃+* localCompletion w :=
  (galCompletion σ w).trans (placeCast hfix)

lemma norm_localAut (x : localCompletion w) : ‖localAut σ w hfix x‖ = ‖x‖ := by
  rw [localAut, RingEquiv.trans_apply, norm_placeCast, norm_galCompletion]

lemma localAut_embedding (x : K') :
    localAut σ w hfix (FinitePlace.embedding w.maximalIdeal x) =
      FinitePlace.embedding w.maximalIdeal (σ x) := by
  rw [localAut, RingEquiv.trans_apply, galCompletion_embedding, placeCast_embedding]

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [Algebra F k]
  [Algebra F K'] [IsScalarTower F k K']

omit [NumberField k] [NumberField K'] [NumberField F] in
lemma σ_algebraMap (a : F) : σ (algebraMap F K' a) = algebraMap F K' a := by
  rw [IsScalarTower.algebraMap_apply F k K', AlgEquiv.commutes]

/-- The curve `E ×_F K'_w` is fixed by the local automorphism. -/
lemma map_curveLoc_localAut :
    (curveLoc E K' w).map (localAut σ w hfix : localCompletion w →+* localCompletion w) =
      curveLoc E K' w := by
  rw [curveLoc, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  ext <;> simp [WeierstrassCurve.map, localAut_embedding, σ_algebraMap]

omit [NumberField k] [NumberField K'] [NumberField F] in
/-- The curve identity `E ×_F k ×_k K' = E ×_F K'`. -/
lemma map_algebraMap_eq :
    (E.map (algebraMap F k)).map (algebraMap k K') = E.map (algebraMap F K') := by
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]

/-- The points of `E(k)` in `E(K'_w)`. -/
def toLoc (R : (E.map (algebraMap F k)).toAffine.Point) : (curveLoc E K' w).toAffine.Point :=
  pointMap (E.map (algebraMap F K')) (FinitePlace.embedding w.maximalIdeal)
    (pointCongr (map_algebraMap_eq E (k := k) (K' := K'))
      (pointMap (E.map (algebraMap F k)) (algebraMap k K') R))

lemma toLoc_zero : toLoc w E (k := k) 0 = 0 := by
  simp only [toLoc, map_zero]

lemma toLoc_nsmul (n : ℕ) (R : (E.map (algebraMap F k)).toAffine.Point) :
    toLoc w E (n • R) = n • toLoc w E R := by
  simp only [toLoc, map_nsmul]

lemma toLoc_injective : Function.Injective (toLoc w E (k := k)) := by
  unfold toLoc
  exact (pointMap_injective _ _).comp ((pointCongr _).injective.comp (pointMap_injective _ _))

/-- The points of `E(k)` are fixed by the local automorphism. -/
lemma pointMap_localAut_toLoc (R : (E.map (algebraMap F k)).toAffine.Point) :
    pointMap (curveLoc E K' w) (localAut σ w hfix : localCompletion w →+* localCompletion w)
        (toLoc w E R) =
      pointCongr (map_curveLoc_localAut σ w hfix E).symm (toLoc w E R) := by
  cases R with
  | zero =>
    change (pointMap _ _) (toLoc w E 0) = (pointCongr _) (toLoc w E 0)
    rw [toLoc_zero, map_zero, map_zero]
  | some x y h =>
    simp only [toLoc, pointMap_some, pointCongr_some]
    exact some_ext (by rw [RingEquiv.coe_toRingHom, localAut_embedding, AlgEquiv.commutes])
      (by rw [RingEquiv.coe_toRingHom, localAut_embedding, AlgEquiv.commutes])

end Aut

end

end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve IsDedekindDomain.HeightOneSpectrum
open scoped Classical Valued

universe u

section

variable {k : Type*} [Field k] [NumberField k]

lemma norm_two_eq_one_of_notMem {w : FinitePlace k} (h2 : (2 : 𝓞 k) ∉ w.maximalIdeal.asIdeal) :
    ‖(2 : localCompletion w)‖ = 1 := by
  rw [norm_eq_one_iff_valued]
  have : (2 : localCompletion w) =
      FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 k) k 2) := by
    rw [map_ofNat, map_ofNat]
  rw [this, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    valuation_eq_one_iff_notMem]
  exact h2

end

section

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

lemma two_notMem_of_isBadPlace (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) :
    (2 : 𝓞 ↥K) ∉ w.maximalIdeal.asIdeal := by
  obtain ⟨v, hv, hwv⟩ := hw
  rw [Tripod.two_mem_maximalIdeal_iff, Tripod.residueChar_eq_of_liesOver hwv]
  exact hVBad v hv

end

end AbcAdaptation.Reference.Iut

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
/-- The ℓ-torsion of a Tate curve has at most `ℓ²` elements. -/
lemma card_torsion_le : Nat.card ↥(torsion ℓ E) ≤ ℓ * ℓ := by
  rw [S.card_torsion_eq ℓ]
  exact Nat.mul_le_mul (S.card_graphLine_le ℓ) (S.card_range_le ℓ)

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
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors

Adapted from lana-agents/tate-curves-theta at ca6c2279d3cea0690cdb01328e727118d5485d68.
The source declarations use the published Tate parameter, model and coordinate series.
-/

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

open Filter Topology

noncomputable section

variable {K : Type*} [NormedField K] (t : TateParameter K)

@[simp] lemma Xterm_apply (u : Kˣ) (n : ℤ) :
    t.Xterm u n = (t.q : K) ^ n * (u : K) / (1 - (t.q : K) ^ n * (u : K)) ^ 2 := rfl

@[simp] lemma Yterm_apply (u : Kˣ) (n : ℤ) :
    t.Yterm u n = ((t.q : K) ^ n * (u : K)) ^ 2 / (1 - (t.q : K) ^ n * (u : K)) ^ 3 := rfl

lemma X_apply (u : Kˣ) : t.X u = (∑' n : ℤ, t.Xterm u n) - 2 * t.eisenstein 1 := rfl

lemma Y_apply (u : Kˣ) : t.Y u = (∑' n : ℤ, t.Yterm u n) + t.eisenstein 1 := rfl

/-- The real-analytic size `‖qⁿ u‖ = ‖q‖ⁿ ‖u‖` of the base point of the `n`-th term, packaged as
a sequence in `n : ℤ`. It tends to `0` on `atTop` and to `+∞` on `atBot`. -/
private def sizeSeq (u : Kˣ) (n : ℤ) : ℝ := ‖(t.q : K)‖ ^ n * ‖(u : K)‖

private lemma norm_qzpow_mul (u : Kˣ) (n : ℤ) :
    ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := by
  simp only [sizeSeq, norm_mul, norm_zpow]

private lemma sizeSeq_eq_exp (u : Kˣ) (n : ℤ) :
    t.sizeSeq u n = Real.exp (Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖) := by
  have ha : 0 < ‖(t.q : K)‖ := t.norm_q_pos
  have hb : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  simp only [sizeSeq]
  rw [← Real.rpow_intCast ‖(t.q : K)‖ n, Real.rpow_def_of_pos ha, Real.exp_add, Real.exp_log hb]

private lemma tendsto_sizeSeq_atTop (u : Kˣ) : Tendsto (t.sizeSeq u) atTop (𝓝 0) := by
  have ha : 0 < ‖(t.q : K)‖ := t.norm_q_pos
  have hlq : Real.log ‖(t.q : K)‖ < 0 := Real.log_neg ha t.norm_lt_one
  have hf : Tendsto
      (fun n : ℤ => Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖) atTop atBot :=
    tendsto_atBot_add_const_right atTop (Real.log ‖(u : K)‖)
      (Tendsto.const_mul_atTop_of_neg hlq tendsto_intCast_atTop_atTop)
  have he : Tendsto
      (fun n : ℤ => Real.exp (Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hf
  exact he.congr fun n => (t.sizeSeq_eq_exp u n).symm

private lemma tendsto_sizeSeq_atBot (u : Kˣ) : Tendsto (t.sizeSeq u) atBot atTop := by
  have ha : 0 < ‖(t.q : K)‖ := t.norm_q_pos
  have hlq : Real.log ‖(t.q : K)‖ < 0 := Real.log_neg ha t.norm_lt_one
  have hf : Tendsto
      (fun n : ℤ => Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖) atBot atTop :=
    tendsto_atTop_add_const_right atBot (Real.log ‖(u : K)‖)
      (Tendsto.const_mul_atBot_of_neg hlq (tendsto_intCast_atBot_iff.2 tendsto_id))
  have he : Tendsto
      (fun n : ℤ => Real.exp (Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖))
      atBot atTop := Real.tendsto_exp_atTop.comp hf
  exact he.congr fun n => (t.sizeSeq_eq_exp u n).symm

section Nonarchimedean

variable [IsUltrametricDist K]

/-- In a nonarchimedean field, `‖1 - x‖ = max 1 ‖x‖` whenever `‖x‖ ≠ 1`: the ultrametric
"isosceles" law makes the norm of the difference the larger of the two norms. -/
lemma norm_one_sub_of_norm_ne_one {x : K} (h : ‖x‖ ≠ 1) : ‖(1 : K) - x‖ = max 1 ‖x‖ := by
  have hne : ‖(1 : K)‖ ≠ ‖-x‖ := by rw [norm_one, norm_neg]; exact h.symm
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, norm_neg]

variable [CompleteSpace K]

/-- **Convergence of the Tate `X`-coordinate series.** Over a complete nonarchimedean field the
family `n ↦ qⁿ u / (1 - qⁿ u)²` is unconditionally summable: its term norm equals `‖q‖ⁿ‖u‖` for
`n → +∞` and `(‖q‖ⁿ‖u‖)⁻¹` for `n → -∞`, both of which tend to `0`. -/
theorem Xterm_summable (u : Kˣ) : Summable (t.Xterm u) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · -- `atBot`: eventually `‖qⁿ u‖ > 1`, so `‖Xterm n‖ = (‖q‖ⁿ‖u‖)⁻¹ → 0`.
    have hlim : Tendsto (fun n : ℤ => (t.sizeSeq u n)⁻¹) atBot (𝓝 0) :=
      (t.tendsto_sizeSeq_atBot u).inv_tendsto_atTop
    refine hlim.congr' ?_
    filter_upwards [(t.tendsto_sizeSeq_atBot u).eventually_gt_atTop 1] with n hn
    have hne0 : t.sizeSeq u n ≠ 0 := (lt_trans one_pos hn).ne'
    have hx : ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := t.norm_qzpow_mul u n
    have hxne : ‖(t.q : K) ^ n * (u : K)‖ ≠ 1 := by rw [hx]; exact ne_of_gt hn
    rw [Xterm_apply, norm_div, norm_pow, norm_one_sub_of_norm_ne_one hxne, hx, max_eq_right hn.le]
    field_simp
  · -- `atTop`: eventually `‖qⁿ u‖ < 1`, so `‖Xterm n‖ = ‖q‖ⁿ‖u‖ → 0`.
    refine (t.tendsto_sizeSeq_atTop u).congr' ?_
    filter_upwards [(t.tendsto_sizeSeq_atTop u).eventually (eventually_lt_nhds one_pos)] with n hn
    have hx : ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := t.norm_qzpow_mul u n
    have hxne : ‖(t.q : K) ^ n * (u : K)‖ ≠ 1 := by rw [hx]; exact ne_of_lt hn
    rw [Xterm_apply, norm_div, norm_pow, norm_one_sub_of_norm_ne_one hxne, hx,
      max_eq_left hn.le, one_pow, div_one]

/-- **Convergence of the Tate `Y`-coordinate series.** Over a complete nonarchimedean field the
family `n ↦ (qⁿ u)² / (1 - qⁿ u)³` is unconditionally summable: its term norm equals `(‖q‖ⁿ‖u‖)²`
for `n → +∞` and `(‖q‖ⁿ‖u‖)⁻¹` for `n → -∞`, both of which tend to `0`. -/
theorem Yterm_summable (u : Kˣ) : Summable (t.Yterm u) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · -- `atBot`: `‖Yterm n‖ = ‖x‖²/‖x‖³ = ‖x‖⁻¹ → 0`.
    have hlim : Tendsto (fun n : ℤ => (t.sizeSeq u n)⁻¹) atBot (𝓝 0) :=
      (t.tendsto_sizeSeq_atBot u).inv_tendsto_atTop
    refine hlim.congr' ?_
    filter_upwards [(t.tendsto_sizeSeq_atBot u).eventually_gt_atTop 1] with n hn
    have hne0 : t.sizeSeq u n ≠ 0 := (lt_trans one_pos hn).ne'
    have hx : ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := t.norm_qzpow_mul u n
    have hxne : ‖(t.q : K) ^ n * (u : K)‖ ≠ 1 := by rw [hx]; exact ne_of_gt hn
    rw [Yterm_apply, norm_div, norm_pow, norm_pow, norm_one_sub_of_norm_ne_one hxne, hx,
      max_eq_right hn.le]
    field_simp
  · -- `atTop`: `‖Yterm n‖ = ‖x‖²/1 = ‖x‖² → 0`.
    have hlim : Tendsto (fun n : ℤ => (t.sizeSeq u n) ^ 2) atTop (𝓝 0) := by
      have := (t.tendsto_sizeSeq_atTop u).pow 2
      simpa using this
    refine hlim.congr' ?_
    filter_upwards [(t.tendsto_sizeSeq_atTop u).eventually (eventually_lt_nhds one_pos)] with n hn
    have hx : ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := t.norm_qzpow_mul u n
    have hxne : ‖(t.q : K) ^ n * (u : K)‖ ≠ 1 := by rw [hx]; exact ne_of_lt hn
    rw [Yterm_apply, norm_div, norm_pow, norm_pow, norm_one_sub_of_norm_ne_one hxne, hx,
      max_eq_left hn.le, one_pow, div_one]

end Nonarchimedean

end

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

noncomputable section

variable {K : Type*} [NormedField K]

/-- Two Tate parameters with the same underlying field element are equal. -/
private lemma eq_of_q_eq {t₁ t₂ : TateParameter K} (h : (t₁.q : K) = (t₂.q : K)) :
    t₁ = t₂ := by
  cases t₁
  cases t₂
  simp only [mk.injEq]
  exact Units.ext h

variable [IsUltrametricDist K] [CompleteSpace K]

section Elliptic

variable (t : TateParameter K)

/-- **The Tate curve is an elliptic curve.** Under the hypothesis `(12 : K) ≠ 0`, the
nonvanishing of the discriminant upgrades `E_q` to a
`WeierstrassCurve.IsElliptic` instance (the current Mathlib replacement for a standalone
`EllipticCurve` structure). -/
theorem tateCurve_isElliptic (h12 : (12 : K) ≠ 0) : t.tateCurve.IsElliptic :=
  ⟨(t.tateCurve_Δ_ne_zero h12).isUnit⟩

/-- `tateJ` agrees with Mathlib's `j`-invariant of the elliptic curve `E_q`. -/
lemma tateJ_eq_j (h12 : (12 : K) ≠ 0) :
    haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
    t.tateJ = t.tateCurve.j := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  rw [WeierstrassCurve.j, tateJ, div_eq_inv_mul]
  congr 1
  rw [← WeierstrassCurve.coe_Δ', ← Units.val_inv_eq_inv_val]

end Elliptic

variable (t₁ t₂ : TateParameter K)

/-- **The discriminant is an isometry in the Tate parameter**:
`‖Δ(E_{q₁}) - Δ(E_{q₂})‖ = ‖q₁ - q₂‖`, by the ultrametric isosceles law applied to the
degree-`≥ 2` estimate for `Δ - q` (`(12 : K) ≠ 0`). -/
theorem norm_tateCurve_Δ_sub_Δ (h12 : (12 : K) ≠ 0) :
    ‖t₁.tateCurve.Δ - t₂.tateCurve.Δ‖ = ‖(t₁.q : K) - (t₂.q : K)‖ := by
  by_cases hq : (t₁.q : K) = (t₂.q : K)
  · rw [eq_of_q_eq hq]
    simp
  · have hD : 0 < ‖(t₁.q : K) - (t₂.q : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
    have hM1 : max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ < 1 := max_lt t₁.norm_lt_one t₂.norm_lt_one
    have hlt : ‖(t₁.tateCurve.Δ - (t₁.q : K)) - (t₂.tateCurve.Δ - (t₂.q : K))‖
        < ‖(t₁.q : K) - (t₂.q : K)‖ :=
      (t₁.norm_tateCurve_Δ_sub_q_sub_le t₂ h12).trans_lt (mul_lt_of_lt_one_left hD hM1)
    rw [show t₁.tateCurve.Δ - t₂.tateCurve.Δ
        = ((t₁.q : K) - (t₂.q : K))
          + ((t₁.tateCurve.Δ - (t₁.q : K)) - (t₂.tateCurve.Δ - (t₂.q : K))) from by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

/-- **The `j`-isometry**: `‖j(E_{q₁}) - j(E_{q₂})‖ = ‖q₁ - q₂‖ / (‖q₁‖ · ‖q₂‖)`
(`(12 : K) ≠ 0`). The numerator `c₄₁³·Δ₂ - Δ₁·c₄₂³` decomposes as
`c₄₁³·(Δ₂ - Δ₁) + Δ₁·(c₄₁³ - c₄₂³)`, in which the first summand has exact norm
`‖q₁ - q₂‖` and strictly dominates the second, so the isosceles law applies. -/
theorem norm_tateJ_sub_tateJ (h12 : (12 : K) ≠ 0) :
    ‖t₁.tateJ - t₂.tateJ‖
      = ‖(t₁.q : K) - (t₂.q : K)‖ / (‖(t₁.q : K)‖ * ‖(t₂.q : K)‖) := by
  by_cases hq : (t₁.q : K) = (t₂.q : K)
  · rw [eq_of_q_eq hq]
    simp
  · have hD : 0 < ‖(t₁.q : K) - (t₂.q : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
    have hΔ₁ := t₁.tateCurve_Δ_ne_zero h12
    have hΔ₂ := t₂.tateCurve_Δ_ne_zero h12
    have hkey : t₁.tateJ - t₂.tateJ
        = (t₁.tateCurve.c₄ ^ 3 * t₂.tateCurve.Δ - t₁.tateCurve.Δ * t₂.tateCurve.c₄ ^ 3)
          / (t₁.tateCurve.Δ * t₂.tateCurve.Δ) := by
      rw [tateJ_def, tateJ_def, div_sub_div _ _ hΔ₁ hΔ₂]
    have h1 : ‖t₁.tateCurve.c₄ ^ 3 * (t₂.tateCurve.Δ - t₁.tateCurve.Δ)‖
        = ‖(t₁.q : K) - (t₂.q : K)‖ := by
      rw [norm_mul, norm_pow, t₁.norm_tateCurve_c₄, one_pow, one_mul,
        t₂.norm_tateCurve_Δ_sub_Δ t₁ h12]
      exact norm_sub_rev _ _
    have h2 : ‖t₁.tateCurve.Δ * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3)‖
        < ‖(t₁.q : K) - (t₂.q : K)‖ := by
      calc ‖t₁.tateCurve.Δ * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3)‖
          = ‖t₁.tateCurve.Δ‖ * ‖t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3‖ := norm_mul _ _
        _ ≤ ‖(t₁.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
            rw [t₁.norm_tateCurve_Δ h12]
            exact mul_le_mul_of_nonneg_left (t₁.norm_tateCurve_c₄_cube_sub_le t₂)
              (norm_nonneg _)
        _ < ‖(t₁.q : K) - (t₂.q : K)‖ := mul_lt_of_lt_one_left hD t₁.norm_lt_one
    have hnum : ‖t₁.tateCurve.c₄ ^ 3 * t₂.tateCurve.Δ - t₁.tateCurve.Δ * t₂.tateCurve.c₄ ^ 3‖
        = ‖(t₁.q : K) - (t₂.q : K)‖ := by
      rw [show t₁.tateCurve.c₄ ^ 3 * t₂.tateCurve.Δ - t₁.tateCurve.Δ * t₂.tateCurve.c₄ ^ 3
          = t₁.tateCurve.c₄ ^ 3 * (t₂.tateCurve.Δ - t₁.tateCurve.Δ)
            + t₁.tateCurve.Δ * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3) from by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2.ne'), h1,
        max_eq_left h2.le]
    rw [hkey, norm_div, hnum, norm_mul, t₁.norm_tateCurve_Δ h12, t₂.norm_tateCurve_Δ h12]

/-- **Injectivity of `q ↦ j(E_q)`**: distinct Tate parameters have distinct `j`-invariants
(`(12 : K) ≠ 0`). -/
theorem tateJ_injective (h12 : (12 : K) ≠ 0) (h : t₁.tateJ = t₂.tateJ) : t₁ = t₂ := by
  have h0 := t₁.norm_tateJ_sub_tateJ t₂ h12
  rw [h, sub_self, norm_zero] at h0
  have hpos : 0 < ‖(t₁.q : K)‖ * ‖(t₂.q : K)‖ := mul_pos t₁.norm_q_pos t₂.norm_q_pos
  rcases div_eq_zero_iff.mp h0.symm with hD | hP
  · exact eq_of_q_eq (sub_eq_zero.mp (norm_eq_zero.mp hD))
  · exact absurd hP hpos.ne'

end

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

noncomputable section

variable {K : Type*} [NormedField K]
variable (L : Type*) [NormedField L] [NormedAlgebra K L]

/-- **Base change** of a Tate parameter along a complete field extension `L / K`.

The underlying unit is the image of `q` under `algebraMap K L`, and `‖·‖ < 1` is preserved
because `‖algebraMap K L q‖ = ‖q‖` (the absolute value of `L` extends that of `K`). -/
def baseChange (t : TateParameter K) : TateParameter L where
  q := Units.map (algebraMap K L).toMonoidHom t.q
  norm_lt_one := by
    have h : ‖((Units.map (algebraMap K L).toMonoidHom t.q : Lˣ) : L)‖ = ‖(t.q : K)‖ := by
      rw [Units.coe_map]
      exact norm_algebraMap' L (t.q : K)
    rw [h]
    exact t.norm_lt_one

@[simp]
lemma baseChange_q_coe (t : TateParameter K) :
    ((t.baseChange L).q : L) = algebraMap K L (t.q : K) :=
  Units.coe_map _ _

variable (t : TateParameter K)

/-- The underlying element of the image of a unit under the algebra map. -/
lemma coe_units_map_algebraMap (u : Kˣ) :
    ((Units.map (algebraMap K L).toMonoidHom u : Lˣ) : L) = algebraMap K L (u : K) :=
  Units.coe_map _ _

/-- The algebra map of an isometric extension maps convergent sums to convergent sums. -/
private lemma algebraMap_tsum' {ι : Type*} {f : ι → K} (hf : Summable f) :
    algebraMap K L (∑' i : ι, f i) = ∑' i : ι, algebraMap K L (f i) :=
  ((hf.hasSum.map (algebraMap K L)
    (AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap' L)).continuous).tsum_eq).symm

/-! ### The general terms -/

/-- The general term of the `X`-coordinate series commutes with an isometric extension. -/
lemma algebraMap_Xterm (u : Kˣ) (n : ℤ) :
    algebraMap K L (t.Xterm u n)
      = (t.baseChange L).Xterm (Units.map (algebraMap K L).toMonoidHom u) n := by
  rw [Xterm_apply, Xterm_apply, map_div₀, map_pow, map_sub, map_one, map_mul, map_zpow₀,
    baseChange_q_coe, coe_units_map_algebraMap]

/-- The general term of the `Y`-coordinate series commutes with an isometric extension. -/
lemma algebraMap_Yterm (u : Kˣ) (n : ℤ) :
    algebraMap K L (t.Yterm u n)
      = (t.baseChange L).Yterm (Units.map (algebraMap K L).toMonoidHom u) n := by
  rw [Yterm_apply, Yterm_apply, map_div₀, map_pow, map_pow, map_sub, map_one, map_mul,
    map_zpow₀, baseChange_q_coe, coe_units_map_algebraMap]

section Coordinates

variable [IsUltrametricDist K] [CompleteSpace K]

/-- The Eisenstein series `sₖ(q)` commutes with an isometric complete extension. -/
lemma algebraMap_eisenstein (k : ℕ) :
    algebraMap K L (t.eisenstein k) = (t.baseChange L).eisenstein k := by
  simp only [eisenstein]
  rw [algebraMap_tsum' L (t.eisenstein_summand_summable k)]
  refine tsum_congr fun n => ?_
  simp only [map_div₀, map_mul, map_pow, map_natCast, map_sub, map_one, baseChange_q_coe]

/-- The Tate coefficient `a₄(q)` commutes with an isometric complete extension. -/
lemma algebraMap_a₄ : algebraMap K L t.a₄ = (t.baseChange L).a₄ := by
  simp only [a₄_def, map_mul, map_neg, map_ofNat, t.algebraMap_eisenstein L]

/-- The Tate coefficient `a₆(q)` commutes with an isometric complete extension. -/
lemma algebraMap_a₆ : algebraMap K L t.a₆ = (t.baseChange L).a₆ := by
  simp only [a₆_def, map_div₀, map_neg, map_add, map_mul, map_ofNat,
    t.algebraMap_eisenstein L]

/-- The Tate `X`-coordinate commutes with an isometric extension. -/
theorem algebraMap_X (u : Kˣ) :
    algebraMap K L (t.X u) = (t.baseChange L).X (Units.map (algebraMap K L).toMonoidHom u) := by
  rw [X_apply, X_apply, map_sub, map_mul, map_ofNat, t.algebraMap_eisenstein L,
    algebraMap_tsum' L (t.Xterm_summable u)]
  congr 1
  exact tsum_congr fun n => t.algebraMap_Xterm L u n

/-- The Tate `Y`-coordinate commutes with an isometric extension. -/
theorem algebraMap_Y (u : Kˣ) :
    algebraMap K L (t.Y u) = (t.baseChange L).Y (Units.map (algebraMap K L).toMonoidHom u) := by
  rw [Y_apply, Y_apply, map_add, t.algebraMap_eisenstein L,
    algebraMap_tsum' L (t.Yterm_summable u)]
  congr 1
  exact tsum_congr fun n => t.algebraMap_Yterm L u n

/-! ### The Tate curve and its `j`-invariant -/

/-- The Tate Weierstrass curve `E_q` base-changes to the Tate curve of the base-changed
parameter. -/
theorem map_tateCurve : t.tateCurve.map (algebraMap K L) = (t.baseChange L).tateCurve := by
  simp only [WeierstrassCurve.map, tateCurve, map_one, map_zero, t.algebraMap_a₄ L,
    t.algebraMap_a₆ L]

end Coordinates

end

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/TateStructureTransport.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: Mathlib compatibility adaptation in the JoshiTeich reference port
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# Transport of Tate structures along isometric isomorphisms

For an isometric field isomorphism `k ≃ k'` of complete rank-one valued fields, written as a
bijective `algebraMap k k'` of a normed algebra, a Tate structure on `E` over `k` transports to a
Tate structure on `E ×_k k'` (`AbcAdaptation.Reference.Iut.TateStructure.baseChange`): the Tate parameter, the change of
variables and the points are mapped along the isomorphism, and the coordinate pins transport by
the naturality of the Tate parametrization (`TateCurvesTheta`, `algebraMap_X`, `algebraMap_Y`).
The graph line and the canonical generators of the transported structure are the images of
those of the original one (`graphLine_baseChange`, `isCanonical_baseChange`).
-/

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve TateCurvesTheta Anabelian
open scoped Classical Valued

universe u v

noncomputable section

section PointMapEquiv

variable {k : Type u} {k' : Type v} [Field k] [Field k'] (E : WeierstrassCurve k)
  (f : k →+* k') (hbij : Function.Bijective f)

/-- The isomorphism on points induced by a bijective ring homomorphism. -/
def pointMapEquiv : E.toAffine.Point ≃+ (E.map f).toAffine.Point :=
  AddEquiv.ofBijective (pointMap E f) ⟨pointMap_injective E f, fun P => by
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x' y' h =>
      obtain ⟨x, rfl⟩ := hbij.2 x'
      obtain ⟨y, rfl⟩ := hbij.2 y'
      exact ⟨.some x y ((E.toAffine.map_nonsingular hbij.1 x y).mp h), rfl⟩⟩

@[simp] lemma pointMapEquiv_apply (P : E.toAffine.Point) :
    pointMapEquiv E f hbij P = pointMap E f P := rfl

/-- Coordinates in the model `C • E` are natural in the base field. -/
lemma xCoord_pointMap (C : VariableChange k) (P : E.toAffine.Point) :
    xCoord (C.map f) (pointMap E f P) = f (xCoord C P) := by
  cases P with
  | zero =>
    change (0 : k') = f 0
    rw [map_zero]
  | some x y h =>
    rw [pointMap_some]
    change (f x - f C.r) / ((Units.map (f : k →* k') C.u : k') ^ 2) = f ((x - C.r) / (C.u : k) ^ 2)
    rw [Units.coe_map, map_div₀, map_sub, map_pow]
    rfl

lemma yCoord_pointMap (C : VariableChange k) (P : E.toAffine.Point) :
    yCoord (C.map f) (pointMap E f P) = f (yCoord C P) := by
  cases P with
  | zero =>
    change (0 : k') = f 0
    rw [map_zero]
  | some x y h =>
    rw [pointMap_some]
    change (f y - f C.t - f C.s * (f x - f C.r)) / ((Units.map (f : k →* k') C.u : k') ^ 3) =
      f ((y - C.t - C.s * (x - C.r)) / (C.u : k) ^ 3)
    rw [Units.coe_map, map_div₀, map_sub, map_sub, map_mul, map_sub, map_pow]
    rfl

end PointMapEquiv

section Transport

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {k' : Type v} [Field k'] [Valued k' (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k' (WithZero (Multiplicative ℤ)))] [CompleteSpace k']
variable [NormedAlgebra k k'] (hbij : Function.Bijective (algebraMap k k'))

/-- The isomorphism on units induced by a bijective `algebraMap`. -/
def unitsEquiv : kˣ ≃* k'ˣ :=
  Units.mapEquiv (MulEquiv.ofBijective (algebraMap k k' : k →* k') hbij)

omit [CompleteSpace k] [CompleteSpace k'] in
lemma coe_unitsEquiv (u : kˣ) : ((unitsEquiv hbij u : k'ˣ) : k') = algebraMap k k' u := rfl

variable (t : TateParameter k)

omit [CompleteSpace k] [CompleteSpace k'] in
lemma map_zpowers_q :
    (Subgroup.zpowers t.q).map (unitsEquiv hbij).toMonoidHom = Subgroup.zpowers (t.baseChange k').q := by
  rw [MonoidHom.map_zpowers]
  congr 1

/-- The isomorphism of analytic quotients `kˣ/qᶻ ≃ k'ˣ/q'ᶻ`. -/
def quotEquiv : kˣ ⧸ Subgroup.zpowers t.q ≃* k'ˣ ⧸ Subgroup.zpowers (t.baseChange k').q :=
  QuotientGroup.congr _ _ (unitsEquiv hbij) (map_zpowers_q hbij t)

omit [CompleteSpace k] [CompleteSpace k'] in
lemma quotEquiv_mk (u : kˣ) :
    quotEquiv hbij t (QuotientGroup.mk u) = QuotientGroup.mk (unitsEquiv hbij u) := rfl

lemma notMem_of_notMem {u : kˣ} (hu : ∀ n : ℤ, ((t.baseChange k').q : k') ^ n *
    ((unitsEquiv hbij u : k'ˣ) : k') ≠ 1) : ∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1 := by
  intro n hn
  apply hu n
  rw [TateParameter.baseChange_q_coe, coe_unitsEquiv, ← map_zpow₀ (algebraMap k k'),
    ← map_mul (algebraMap k k'), hn, map_one]

variable {E : WeierstrassCurve k}

namespace TateStructure

/-- **Transport of a Tate structure** along a bijective isometric base change. -/
def baseChange (S : TateStructure E) : TateStructure (E.map (algebraMap k k')) where
  t := S.t.baseChange k'
  C := S.C.map (algebraMap k k')
  hC := by rw [map_variableChange, S.hC, S.t.map_tateCurve k']
  iso := (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm.trans
    (S.iso.trans (pointMapEquiv E (algebraMap k k') hbij))
  iso_x u' hu' := by
    obtain ⟨u, rfl⟩ := (unitsEquiv hbij).surjective u'
    have hu := notMem_of_notMem hbij S.t hu'
    have h1 : (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm
        (Additive.ofMul (QuotientGroup.mk (unitsEquiv hbij u))) =
        Additive.ofMul (QuotientGroup.mk u) := by
      rw [← quotEquiv_mk]
      change Additive.ofMul ((quotEquiv hbij S.t).symm
        ((quotEquiv hbij S.t) (QuotientGroup.mk u))) = _
      rw [(quotEquiv hbij S.t).symm_apply_apply]
    simp only [AddEquiv.trans_apply]
    rw [h1, pointMapEquiv_apply, xCoord_pointMap, S.iso_x u hu, S.t.algebraMap_X k']
    rfl
  iso_y u' hu' := by
    obtain ⟨u, rfl⟩ := (unitsEquiv hbij).surjective u'
    have hu := notMem_of_notMem hbij S.t hu'
    have h1 : (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm
        (Additive.ofMul (QuotientGroup.mk (unitsEquiv hbij u))) =
        Additive.ofMul (QuotientGroup.mk u) := by
      rw [← quotEquiv_mk]
      change Additive.ofMul ((quotEquiv hbij S.t).symm
        ((quotEquiv hbij S.t) (QuotientGroup.mk u))) = _
      rw [(quotEquiv hbij S.t).symm_apply_apply]
    simp only [AddEquiv.trans_apply]
    rw [h1, pointMapEquiv_apply, yCoord_pointMap, S.iso_y u hu, S.t.algebraMap_Y k']
    rfl

variable (S : TateStructure E)

lemma baseChange_ofUnit (u : kˣ) :
    (S.baseChange hbij).ofUnit (unitsEquiv hbij u) = pointMap E (algebraMap k k') (S.ofUnit u) := by
  unfold ofUnit
  change ((MulEquiv.toAdditive (quotEquiv hbij S.t)).symm.trans
    (S.iso.trans (pointMapEquiv E (algebraMap k k') hbij)))
      (Additive.ofMul (QuotientGroup.mk (unitsEquiv hbij u) :
        k'ˣ ⧸ Subgroup.zpowers (S.t.baseChange k').q)) = _
  have h1 : (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm
      (Additive.ofMul (QuotientGroup.mk (unitsEquiv hbij u))) =
      Additive.ofMul (QuotientGroup.mk u) := by
    rw [← quotEquiv_mk]
    change Additive.ofMul ((quotEquiv hbij S.t).symm
      ((quotEquiv hbij S.t) (QuotientGroup.mk u))) = _
    rw [(quotEquiv hbij S.t).symm_apply_apply]
  simp only [AddEquiv.trans_apply]
  rw [h1]
  rfl

end TateStructure

end Transport

end

end AbcAdaptation.Reference.Iut

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/TateStructureUnique.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: copied into the JoshiTeich reference namespace; imports are adapted to local modules
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# Uniqueness of Tate structures

Two Tate structures on the same elliptic curve `E` over `k` have the same Tate parameter
(`j(E_q) = j(E)` determines `q`, `TateParameter.tateJ_injective`) and point maps that agree
up to a global sign: the changes of variables `C`, `C'` with `C • E = C' • E = E_q` differ by
an automorphism of `E_q`, and the only automorphisms of `E_q` are `1` and the negation
`(u, r, s, t) = (-1, 0, -1, 0)` (`AbcAdaptation.Reference.Iut.eq_one_or_negChange_of_smul_tateCurve`), which acts as
`P ↦ -P` on points. Consequently the graph line and the canonical generators do not depend
on the Tate structure (`AbcAdaptation.Reference.Iut.TateStructure.graphLine_eq`, `isCanonical_congr`).
-/

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve TateCurvesTheta AbcAdaptation.Reference.Iut.Anabelian
open scoped Classical Valued

universe u

noncomputable section

section Composition

variable {k : Type*} [Field k]

lemma vcX_mul (D C : VariableChange k) (x : k) : vcX (D * C) x = vcX D (vcX C x) := by
  simp only [vcX, VariableChange.mul_def, Units.val_mul]
  have hu := u_ne_zero C
  have hv := u_ne_zero D
  field_simp
  ring

lemma vcY_mul (D C : VariableChange k) (x y : k) :
    vcY (D * C) x y = vcY D (vcX C x) (vcY C x y) := by
  simp only [vcX, vcY, VariableChange.mul_def, Units.val_mul]
  have hu := u_ne_zero C
  have hv := u_ne_zero D
  field_simp
  ring

variable (k) in
/-- The negation change of variables `(-1, 0, -1, 0)`. -/
def negChange : VariableChange k := ⟨-1, 0, -1, 0⟩

lemma vcX_negChange (x : k) : vcX (negChange k) x = x := by
  simp [vcX, negChange]

lemma vcY_negChange (x y : k) : vcY (negChange k) x y = -y - x := by
  simp only [vcY, negChange]
  rw [Units.val_neg, Units.val_one]
  ring

end Composition

section Coordinates

variable {k : Type u} [Field k] {E : WeierstrassCurve k}

lemma xCoord_mul (D C : VariableChange k) {P : E.toAffine.Point} (hP : P ≠ 0) :
    xCoord (D * C) P = vcX D (xCoord C P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact vcX_mul D C x

lemma yCoord_mul (D C : VariableChange k) {P : E.toAffine.Point} (hP : P ≠ 0) :
    yCoord (D * C) P = vcY D (xCoord C P) (yCoord C P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact vcY_mul D C x y

lemma xCoord_neg (C : VariableChange k) (P : E.toAffine.Point) :
    xCoord C (-P) = xCoord C P := by
  cases P <;> rfl

lemma yCoord_neg (C : VariableChange k) {P : E.toAffine.Point} (hP : P ≠ 0) :
    yCoord C (-P) = (C • E).toAffine.negY (xCoord C P) (yCoord C P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    rw [Affine.Point.neg_some]
    exact vcY_negY C E x y

/-- Nonzero points with the same coordinates in a model are equal. -/
lemma eq_of_coords (C : VariableChange k) {P Q : E.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : xCoord C P = xCoord C Q) (hy : yCoord C P = yCoord C Q) : P = Q := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    cases Q with
    | zero => exact absurd rfl hQ
    | some x' y' h' =>
      change vcX C x = vcX C x' at hx
      change vcY C x y = vcY C x' y' at hy
      have hxx := vcX_injective C hx
      subst hxx
      rw [vcY_inj] at hy
      subst hy
      rfl

end Coordinates

section Aut

variable {k : Type u} [NormedField k] [IsUltrametricDist k] [CompleteSpace k]

/-- **The automorphisms of a Tate curve** are `1` and the negation. -/
theorem eq_one_or_negChange_of_smul_tateCurve (t : TateParameter k) (h12 : (12 : k) ≠ 0)
    {D : VariableChange k} (hD : D • t.tateCurve = t.tateCurve) : D = 1 ∨ D = negChange k := by
  have h2 : (2 : k) ≠ 0 := by
    intro h
    apply h12
    rw [show (12 : k) = 2 * 6 by norm_num, h, zero_mul]
  have h3 : (3 : k) ≠ 0 := by
    intro h
    apply h12
    rw [show (12 : k) = 3 * 4 by norm_num, h, zero_mul]
  have hc₄ : t.tateCurve.c₄ ≠ 0 := by
    intro h
    have := t.norm_tateCurve_c₄
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hc₆ : t.tateCurve.c₆ ≠ 0 := by
    intro h
    have := norm_c₆_eq_one t.tateCurve t.norm_tateCurve_c₄ (by rw [t.norm_tateCurve_Δ h12]; exact t.norm_lt_one)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hu0 := D.u.ne_zero
  have hu4 : (D.u : k) ^ 4 = 1 := by
    have h := variableChange_c₄ (W := t.tateCurve) (C := D)
    rw [hD, Units.val_inv_eq_inv_val, inv_pow] at h
    have h' : t.tateCurve.c₄ * (D.u : k) ^ 4 = t.tateCurve.c₄ := by
      calc t.tateCurve.c₄ * (D.u : k) ^ 4
          = ((D.u : k) ^ 4)⁻¹ * t.tateCurve.c₄ * (D.u : k) ^ 4 := by rw [← h]
        _ = t.tateCurve.c₄ := by field_simp
    have := mul_left_cancel₀ hc₄ (h'.trans (mul_one _).symm)
    exact this
  have hu6 : (D.u : k) ^ 6 = 1 := by
    have h := variableChange_c₆ (W := t.tateCurve) (C := D)
    rw [hD, Units.val_inv_eq_inv_val, inv_pow] at h
    have h' : t.tateCurve.c₆ * (D.u : k) ^ 6 = t.tateCurve.c₆ := by
      calc t.tateCurve.c₆ * (D.u : k) ^ 6
          = ((D.u : k) ^ 6)⁻¹ * t.tateCurve.c₆ * (D.u : k) ^ 6 := by rw [← h]
        _ = t.tateCurve.c₆ := by field_simp
    exact mul_left_cancel₀ hc₆ (h'.trans (mul_one _).symm)
  have hu2 : (D.u : k) * (D.u : k) = 1 := by
    have : (D.u : k) ^ 6 = (D.u : k) ^ 4 * ((D.u : k) * (D.u : k)) := by ring
    rw [hu6, hu4, one_mul] at this
    exact this.symm
  have hu : (D.u : k) = 1 ∨ (D.u : k) = -1 := mul_self_eq_one_iff.mp hu2
  -- the coefficient equations
  have e1 : (D.u : k)⁻¹ * (1 + 2 * D.s) = 1 := by
    have h := variableChange_a₁ (W := t.tateCurve) (C := D)
    rw [hD, t.tateCurve_a₁, Units.val_inv_eq_inv_val] at h
    exact h.symm
  have e2 : (D.u : k)⁻¹ ^ 2 * (0 - D.s * 1 + 3 * D.r - D.s ^ 2) = 0 := by
    have h := variableChange_a₂ (W := t.tateCurve) (C := D)
    rw [hD, t.tateCurve_a₂, t.tateCurve_a₁, Units.val_inv_eq_inv_val] at h
    exact h.symm
  have e3 : (D.u : k)⁻¹ ^ 3 * (0 + D.r * 1 + 2 * D.t) = 0 := by
    have h := variableChange_a₃ (W := t.tateCurve) (C := D)
    rw [hD, t.tateCurve_a₃, t.tateCurve_a₁, Units.val_inv_eq_inv_val] at h
    exact h.symm
  have hu' : (D.u : k)⁻¹ = (D.u : k) := inv_eq_of_mul_eq_one_right hu2
  rw [hu'] at e1 e2 e3
  have hs : D.s = ((D.u : k) - 1) / 2 := by
    have : (D.u : k) * ((D.u : k) * (1 + 2 * D.s)) = (D.u : k) * 1 := by rw [e1]
    rw [← mul_assoc, hu2, one_mul, mul_one] at this
    field_simp
    linear_combination this
  have hr : D.r = 0 := by
    have hpow : (D.u : k) ^ 2 ≠ 0 := pow_ne_zero _ hu0
    have h := (mul_eq_zero.mp e2).resolve_left hpow
    have h3r : 3 * D.r = 0 := by
      rcases hu with hu | hu
      · have hs0 : D.s = 0 := by rw [hs, hu]; norm_num
        rw [hs0] at h
        linear_combination h
      · have hs1 : D.s = -1 := by rw [hs, hu, div_eq_iff h2]; norm_num
        rw [hs1] at h
        linear_combination h
    exact (mul_eq_zero.mp h3r).resolve_left h3
  have ht : D.t = 0 := by
    have hpow : (D.u : k) ^ 3 ≠ 0 := pow_ne_zero _ hu0
    have h := (mul_eq_zero.mp e3).resolve_left hpow
    rw [hr] at h
    have : 2 * D.t = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  rcases hu with hu | hu
  · left
    have hs0 : D.s = 0 := by rw [hs, hu]; norm_num
    ext
    · rw [hu]; rfl
    · rw [hr]; rfl
    · rw [hs0]; rfl
    · rw [ht]; rfl
  · right
    have hs1 : D.s = -1 := by rw [hs, hu, div_eq_iff h2]; norm_num
    ext
    · rw [hu]; rfl
    · rw [hr]; rfl
    · rw [hs1]; rfl
    · rw [ht]; rfl

end Aut

/-! ## Uniqueness up to sign -/

section Unique

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

variable {E : WeierstrassCurve k}

/-- `j` is compatible with equality of curves. -/
lemma j_congr {W W' : WeierstrassCurve k} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

namespace TateStructure

variable (S : TateStructure E)

lemma notMem_zpowers_iff (u : kˣ) :
    u ∉ Subgroup.zpowers S.t.q ↔ ∀ n : ℤ, (S.t.q : k) ^ n * (u : k) ≠ 1 := by
  constructor
  · intro hu n hn
    apply hu
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-n, ?_⟩
    have h' : S.t.q ^ n * u = 1 := Units.ext (by simpa using hn)
    rw [zpow_neg]
    exact inv_eq_of_mul_eq_one_right h'
  · intro hu hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨n, hn⟩ := hmem
    apply hu (-n)
    rw [← hn, Units.val_zpow_eq_zpow_val, zpow_neg,
      inv_mul_cancel₀ (zpow_ne_zero _ S.t.q.ne_zero)]

lemma ofUnit_ne_zero {u : kˣ} (hu : u ∉ Subgroup.zpowers S.t.q) : S.ofUnit u ≠ 0 := by
  intro h
  rw [← S.ofUnit_one, S.ofUnit_eq_iff] at h
  obtain ⟨n, hn⟩ := h
  apply hu
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨-n, ?_⟩
  rw [zpow_neg]
  exact inv_eq_of_mul_eq_one_right hn.symm

lemma ofUnit_eq_zero_of_mem {u : kˣ} (hu : u ∈ Subgroup.zpowers S.t.q) : S.ofUnit u = 0 := by
  rw [Subgroup.mem_zpowers_iff] at hu
  obtain ⟨n, rfl⟩ := hu
  rw [← S.ofUnit_one, S.ofUnit_eq_iff]
  exact ⟨-n, by rw [zpow_neg, inv_mul_cancel]⟩

variable [E.IsElliptic]

/-- **Uniqueness of the Tate parameter.** -/
theorem t_eq (S S' : TateStructure E) (h12 : (12 : k) ≠ 0) : S'.t = S.t := by
  apply TateParameter.tateJ_injective _ _ h12
  haveI := S.t.tateCurve_isElliptic h12
  haveI := S'.t.tateCurve_isElliptic h12
  rw [S.t.tateJ_eq_j h12, S'.t.tateJ_eq_j h12, ← j_congr S.hC, ← j_congr S'.hC,
    variableChange_j, variableChange_j]

end TateStructure

end Unique

end

end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Reference.Iut.TateStructure

universe u

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

/-- Transport of a Tate structure along an equality of curves. -/
def congr {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) : TateStructure W' := by
  subst h
  exact S

end AbcAdaptation.Reference.Iut.TateStructure

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/TateSign.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `e4777b2238f45be2e58c00b4d0213c0cb83405b9`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: Mathlib compatibility adaptation in the JoshiTeich reference port
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

/-!
# The local sign theorem: `−c₄c₆` is a square fixed by an isometry

Let `E` be an elliptic curve over a complete rank-one valued field `k` carrying a Tate
structure `S` (`AbcAdaptation.Reference.Iut.TateStructure`), and let `σ : k ≃+* k` be an isometric automorphism fixing
the coefficients of `E`. If, for an odd prime `ℓ`, the ℓ-torsion `E(k)[ℓ]` has `ℓ²` elements
all of which are fixed by `σ`, then `−c₄(E)c₆(E)` has a **`σ`-fixed square root** in `k`
(`AbcAdaptation.Reference.Iut.exists_sqrt_neg_c₄_mul_c₆_fixed`).

The proof transports the Tate structure along `σ` (`AbcAdaptation.Reference.Iut.TateStructure.baseChange` on the type
synonym `AbcAdaptation.Reference.Iut.Twist k`, whose `k`-algebra structure is `σ`), obtaining a second Tate structure
`S'` on `E` with `S'.C = S.C.map σ` and `S'.ofUnit (σ u) = σ (S.ofUnit u)`. By the uniqueness
of Tate structures (`AbcAdaptation.Reference.Iut.eq_one_or_negChange_of_smul_tateCurve`) the changes of variables `S'.C`
and `S.C` differ by `1` or by the negation of `E_q`; the negation would make `σ` act as `−1`
on the class of an ℓ-th root of `q`, forcing `ℓ ∣ 2`. Hence `S.C.map σ = S.C`, so `σ` fixes
`E_q = S.C • E` and its invariants; Hensel's lemma (`AbcAdaptation.Reference.Iut.exists_sq_eq_of_norm_sq_sub_lt`) gives a
square root `s` of `−c₄(E_q)c₆(E_q) ≡ 1` with `‖s − 1‖ < 1`, which is `σ`-fixed since `−s` is
not close to `1`, and `r = u⁵ s` is the required root for `E`.
-/

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve TateCurvesTheta Anabelian
open scoped Classical Valued

universe u

noncomputable section

/-! ### Transport lemmas -/

section Congr

variable {k : Type u} [Field k]

lemma pointCongr_pointCongr_symm {W W' : WeierstrassCurve k} (h : W = W') (P : W'.toAffine.Point) :
    pointCongr h (pointCongr h.symm P) = P := by
  subst h
  rfl

variable [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

namespace TateStructure

omit [CompleteSpace k] in
lemma congr_t {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) :
    (S.congr h).t = S.t := by
  subst h
  rfl

omit [CompleteSpace k] in
lemma congr_C {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) :
    (S.congr h).C = S.C := by
  subst h
  rfl

omit [CompleteSpace k] in
lemma ofUnit_congr {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) (u : kˣ) :
    (S.congr h).ofUnit u = pointCongr h (S.ofUnit u) := by
  subst h
  rfl

end TateStructure

end Congr

/-! ### The negation of the Tate curve acts as `−1` on points -/

section Neg

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} [E.IsElliptic]

namespace TateStructure

/-- If the changes of variables of two Tate structures differ by the negation of `E_q`, their
point maps differ by the sign `−1` (the second branch of `ofUnit_eq_or_neg`). -/
lemma ofUnit_eq_neg_of_C (S S' : TateStructure E) (h12 : (12 : k) ≠ 0)
    (hC' : S'.C = negChange k * S.C) (u : kˣ) : S'.ofUnit u = -S.ofUnit u := by
  have ht := S.t_eq S' h12
  by_cases hu : u ∈ Subgroup.zpowers S.t.q
  · rw [S'.ofUnit_eq_zero_of_mem (by rw [ht]; exact hu), S.ofUnit_eq_zero_of_mem hu, neg_zero]
  · have hu' : ∀ n : ℤ, (S'.t.q : k) ^ n * (u : k) ≠ 1 := by
      rw [ht]
      exact (S.notMem_zpowers_iff u).mp hu
    have hx : xCoord S'.C (S'.ofUnit u) = S.t.X u := by
      rw [← ht]
      exact S'.iso_x u hu'
    have hy : yCoord S'.C (S'.ofUnit u) = S.t.Y u := by
      rw [← ht]
      exact S'.iso_y u hu'
    have hx' : xCoord S.C (S.ofUnit u) = S.t.X u :=
      S.iso_x u ((S.notMem_zpowers_iff u).mp hu)
    have hy' : yCoord S.C (S.ofUnit u) = S.t.Y u :=
      S.iso_y u ((S.notMem_zpowers_iff u).mp hu)
    have hne' : S'.ofUnit u ≠ 0 := S'.ofUnit_ne_zero (by rw [ht]; exact hu)
    have hne : S.ofUnit u ≠ 0 := S.ofUnit_ne_zero hu
    rw [hC', xCoord_mul _ _ hne', vcX_negChange] at hx
    rw [hC', yCoord_mul _ _ hne', vcY_negChange, hx] at hy
    refine eq_of_coords S.C hne' (neg_ne_zero.mpr hne) ?_ ?_
    · rw [xCoord_neg, hx, hx']
    · rw [yCoord_neg _ hne, hx', hy']
      have hnegY : (S.C • E).toAffine.negY (S.t.X u) (S.t.Y u) = -S.t.Y u - S.t.X u := by
        unfold Affine.negY
        rw [S.hC, S.t.tateCurve_a₁, S.t.tateCurve_a₃]
        ring
      rw [hnegY]
      linear_combination -hy

end TateStructure

end Neg

/-! ### The core argument over `k` -/

section Core

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} [E.IsElliptic]

/-- An odd prime does not divide `2`. -/
lemma not_dvd_two_of_odd_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) : ¬ ℓ ∣ 2 := fun h =>
  hodd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h)

/-- **The change of variables is fixed.** Given a second Tate structure `S'` on `E` obtained by
transporting `S` along an endomorphism `f` of `k` fixing `E`, if the ℓ-torsion is `f`-fixed
and has `ℓ²` elements (`ℓ` an odd prime), then `f` fixes the Tate parameter and the change of
variables of `S`. -/
theorem TateStructure.map_eq_of_fixed (f : k →+* k) (hE : E.map f = E) (h12 : (12 : k) ≠ 0)
    (S S' : TateStructure E) (hq : S'.t.q = Units.map f.toMonoidHom S.t.q)
    (hC : S'.C = S.C.map f)
    (hS' : ∀ u : kˣ, S'.ofUnit (Units.map f.toMonoidHom u) =
      pointCongr hE (pointMap E f (S.ofUnit u)))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (htors : ∀ P ∈ TateStructure.torsion ℓ E, pointMap E f P = pointCongr hE.symm P)
    (hcard : ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ E)) :
    Units.map f.toMonoidHom S.t.q = S.t.q ∧ S.C.map f = S.C := by
  have ht := S.t_eq S' h12
  have hqfix : Units.map f.toMonoidHom S.t.q = S.t.q := by rw [← hq, ht]
  refine ⟨hqfix, ?_⟩
  -- the change of variables of `S'` differs from that of `S` by an automorphism of `E_q`
  set D := S'.C * S.C⁻¹ with hDdef
  have hC' : S'.C = D * S.C := by rw [hDdef, inv_mul_cancel_right]
  have hD : D • S.t.tateCurve = S.t.tateCurve := by
    rw [← S.hC, hDdef, mul_smul, inv_smul_smul, S'.hC, ht, S.hC]
  rcases eq_one_or_negChange_of_smul_tateCurve S.t h12 hD with hD1 | hDn
  · rw [hD1, one_mul] at hC'
    rw [← hC, hC']
  · exfalso
    rw [hDn] at hC'
    have hneg := S.ofUnit_eq_neg_of_C S' h12 hC'
    -- a root class of `q`
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨u, m, hu⟩ := S.exists_root_class ℓ hcard
    have hP : S.ofUnit u ∈ TateStructure.torsion ℓ E := (S.ofUnit_mem_torsionBy_iff ℓ u).mpr ⟨_, hu⟩
    -- its point is `f`-fixed
    have hfix : S'.ofUnit (Units.map f.toMonoidHom u) = S.ofUnit u := by
      rw [hS', htors _ hP, pointCongr_pointCongr_symm]
    rw [hneg, ← TateStructure.ofUnit_inv, TateStructure.ofUnit_eq_iff] at hfix
    obtain ⟨n, hn⟩ := hfix
    -- `f` fixes `u ^ ℓ`
    have hfu : Units.map f.toMonoidHom u ^ ℓ = S.t.q ^ (1 + ℓ * m) := by
      rw [← map_pow, hu, map_zpow, hqfix]
    have hpow : S.t.q ^ (1 + (ℓ : ℤ) * m) = S.t.q ^ ((n * ℓ : ℤ) + -(1 + ℓ * m)) := by
      rw [← hu, hn, mul_pow, inv_pow, hfu, zpow_add S.t.q (n * ℓ) (-(1 + ℓ * m)),
        zpow_mul, zpow_natCast, zpow_neg]
    have hexp := S.q_zpow_injective hpow
    have hdvd : (ℓ : ℤ) ∣ 2 := ⟨n - 2 * m, by linear_combination hexp⟩
    exact not_dvd_two_of_odd_prime hℓ hodd (Int.natCast_dvd_ofNat.mp hdvd)

omit [E.IsElliptic] in
/-- **The square root, given that `f` fixes the change of variables.** -/
theorem TateStructure.exists_sqrt_of_map_C_eq (f : k →+* k) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (hE : E.map f = E) (h2 : ‖(2 : k)‖ = 1) (h12 : (12 : k) ≠ 0) (S : TateStructure E) (hC : S.C.map f = S.C) :
    ∃ r : k, f r = r ∧ r ^ 2 = -(E.c₄ * E.c₆) := by
  -- `f` fixes the Tate curve `E_q = S.C • E`
  have hEq : S.t.tateCurve.map f = S.t.tateCurve := by
    rw [← S.hC, ← map_variableChange, hC, hE]
  have hc4 : f S.t.tateCurve.c₄ = S.t.tateCurve.c₄ := by rw [← map_c₄, hEq]
  have hc6 : f S.t.tateCurve.c₆ = S.t.tateCurve.c₆ := by rw [← map_c₆, hEq]
  set a := -(S.t.tateCurve.c₄ * S.t.tateCurve.c₆) with ha
  have hfa : f a = a := by rw [ha, map_neg, map_mul, hc4, hc6]
  have hlt : ‖(1 : k) ^ 2 - a‖ < 1 := by
    rw [one_pow, ha, sub_neg_eq_add, add_comm]
    exact norm_tateCurve_c₄_mul_c₆_add_one_lt S.t h12
  obtain ⟨s, hs, hs1⟩ := exists_sq_eq_of_norm_sq_sub_lt h2 norm_one hlt
  have hs_norm : ‖s‖ = 1 := norm_eq_one_of_norm_sub_lt_one norm_one hs1
  -- the square root is `f`-fixed
  have hfs : f s = s := by
    have h1 : (f s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, hfa]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact h
    · exfalso
      have hfs1 : ‖f s - 1‖ < 1 := by
        rw [← map_one f, ← map_sub, hf]
        exact hs1
      have hdiff : ‖(f s - 1) - (s - 1)‖ = 1 := by
        rw [h, show (-s - 1) - (s - 1) = -(2 * s) by ring, norm_neg, norm_mul, h2, hs_norm,
          one_mul]
      have hle : ‖(f s - 1) - (s - 1)‖ < 1 := by
        rw [sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hfs1 ?_)
        rw [norm_neg]
        exact hs1
      rw [hdiff] at hle
      exact lt_irrefl _ hle
  -- `f` fixes the scaling unit of `S.C`
  have hCu : f (S.C.u : k) = S.C.u := by
    have := congrArg (fun C : VariableChange k => (C.u : k)) hC
    exact this
  have hc4' : S.t.tateCurve.c₄ = (S.C.u : k)⁻¹ ^ 4 * E.c₄ := by
    rw [← S.hC, variableChange_c₄, Units.val_inv_eq_inv_val]
  have hc6' : S.t.tateCurve.c₆ = (S.C.u : k)⁻¹ ^ 6 * E.c₆ := by
    rw [← S.hC, variableChange_c₆, Units.val_inv_eq_inv_val]
  refine ⟨(S.C.u : k) ^ 5 * s, by rw [map_mul, map_pow, hCu, hfs], ?_⟩
  rw [mul_pow, ← pow_mul, hs, ha, hc4', hc6']
  have hu0 : (S.C.u : k) ≠ 0 := S.C.u.ne_zero
  field_simp

end Core

/-! ### The twisted field -/

section Twist

variable (k : Type u) [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

/-- A type synonym for `k`, to be made a normed `k`-algebra through an isometric automorphism
`σ` of `k` (so that `algebraMap k (Twist k) = σ`). -/
def Twist : Type u := k

instance : Field (Twist k) := inferInstanceAs (Field k)

instance : Valued (Twist k) (WithZero (Multiplicative ℤ)) :=
  inferInstanceAs (Valued k (WithZero (Multiplicative ℤ)))

instance : Valuation.RankOne (Valued.v : Valuation (Twist k) (WithZero (Multiplicative ℤ))) :=
  inferInstanceAs (Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ))))

instance : CompleteSpace (Twist k) := inferInstanceAs (CompleteSpace k)

variable {k}

/-- The `k`-algebra structure on `Twist k` through `σ`. -/
@[reducible] def twistAlgebra (σ : k ≃+* k) : Algebra k (Twist k) :=
  ((σ : k →+* k) : k →+* Twist k).toAlgebra

/-- The normed `k`-algebra structure on `Twist k` through an isometric `σ`. -/
@[reducible] def twistNormedAlgebra (σ : k ≃+* k) (hσ : ∀ x, ‖σ x‖ = ‖x‖) : NormedAlgebra k (Twist k) :=
  @NormedAlgebra.mk _ _ _ _ (twistAlgebra σ) fun r x => by
    letI := twistAlgebra σ
    rw [Algebra.smul_def, norm_mul]
    have h : ‖algebraMap k (Twist k) r‖ = ‖r‖ := hσ r
    rw [h]

end Twist

/-! ### The local sign theorem -/

section Main

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

/-- **The local sign theorem.** Let `σ` be an isometric automorphism of `k` fixing the
coefficients of an elliptic curve `E` with a Tate structure `S`, and let `ℓ` be an odd prime
such that `E(k)[ℓ]` has at least `ℓ²` elements, all fixed by `σ`. Then `−c₄(E)c₆(E)` has a
`σ`-fixed square root. -/
theorem exists_sqrt_neg_c₄_mul_c₆_fixed (σ : k ≃+* k) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (E : WeierstrassCurve k) [E.IsElliptic] (hE : E.map (σ : k →+* k) = E)
    (h2 : ‖(2 : k)‖ = 1) (h12 : (12 : k) ≠ 0) (S : TateStructure E) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (htors : ∀ P ∈ TateStructure.torsion ℓ E,
      pointMap E (σ : k →+* k) P = pointCongr hE.symm P)
    (hcard : ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ E)) :
    ∃ r : k, σ r = r ∧ r ^ 2 = -(E.c₄ * E.c₆) := by
  letI := twistNormedAlgebra σ hσ
  have hbij : Function.Bijective (algebraMap k (Twist k)) := σ.bijective
  have hE' : E.map (algebraMap k (Twist k)) = (E : WeierstrassCurve (Twist k)) := hE
  -- the transported Tate structure, read as a Tate structure on `E` over `k`
  have hq : ((S.baseChange hbij).congr hE').t.q =
      Units.map (σ : k →+* k).toMonoidHom S.t.q := by
    rw [TateStructure.congr_t hE' (S.baseChange hbij)]
    rfl
  have hC : ((S.baseChange hbij).congr hE').C = S.C.map (σ : k →+* k) := by
    rw [TateStructure.congr_C hE' (S.baseChange hbij)]
    rfl
  have hS' : ∀ u : kˣ, ((S.baseChange hbij).congr hE').ofUnit
      (Units.map (σ : k →+* k).toMonoidHom u) =
      pointCongr hE (pointMap E (σ : k →+* k) (S.ofUnit u)) := fun u => by
    have h := (TateStructure.ofUnit_congr hE' (S.baseChange hbij) (unitsEquiv hbij u)).trans
      (congrArg _ (S.baseChange_ofUnit hbij u))
    exact h
  obtain ⟨-, hCfix⟩ := TateStructure.map_eq_of_fixed (σ : k →+* k) hE h12 S
    ((S.baseChange hbij).congr hE') hq hC hS' hℓ hodd htors hcard
  obtain ⟨r, hr, hr2⟩ := TateStructure.exists_sqrt_of_map_C_eq (σ : k →+* k) hσ hE h2 h12 S hCfix
  exact ⟨r, hr, hr2⟩

end Main

end

end AbcAdaptation.Reference.Iut

/-
original-path: `refer/iut/Iut/Cor312/ThetaData/SqrtAtBadPlace.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `e4777b2238f45be2e58c00b4d0213c0cb83405b9`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: Mathlib compatibility adaptation in the JoshiTeich reference port
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve AbcAdaptation.Reference.Iut.Anabelian TateCurvesTheta
open IsDedekindDomain.HeightOneSpectrum
open scoped Classical Valued

universe u

noncomputable section

/-! ## Transitivity of lying over -/

section Trans

variable {A B C : Type*} [Field A] [NumberField A] [Field B] [NumberField B] [Field C]
  [NumberField C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

lemma FinitePlace.liesOver_trans {w₃ : FinitePlace C} {w₂ : FinitePlace B} {w₁ : FinitePlace A}
    (h₁ : FinitePlace.LiesOver w₃ w₂) (h₂ : FinitePlace.LiesOver w₂ w₁) :
    FinitePlace.LiesOver w₃ w₁ := by
  haveI : w₃.maximalIdeal.asIdeal.LiesOver w₂.maximalIdeal.asIdeal := h₁
  haveI : w₂.maximalIdeal.asIdeal.LiesOver w₁.maximalIdeal.asIdeal := h₂
  exact Ideal.LiesOver.trans w₃.maximalIdeal.asIdeal w₂.maximalIdeal.asIdeal
    w₁.maximalIdeal.asIdeal

end Trans

/-! ## The setting -/

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := 1100) instDecidableEqIntermediateField''' : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

section NormsAt

variable {K' : Type u} [Field K'] [NumberField K'] [Algebra F K'] {w : FinitePlace K'}
  {w₀ : FinitePlace F} (hww₀ : FinitePlace.LiesOver w w₀)
  (hc₄ : w₀.maximalIdeal.valuation F E.c₄ = 1) (hΔ : w₀.maximalIdeal.valuation F E.Δ < 1)

omit [E.IsElliptic] in
include hww₀ hc₄ in
/-- `‖c₄‖ = 1` over `K'_w` for a model `E` with `v_{w₀}(c₄(E)) = 1` at the place `w₀` below `w`. -/
lemma norm_c₄_curveLoc : ‖(curveLoc E K' w).c₄‖ = 1 := by
  rw [curveLoc, map_c₄, map_c₄, norm_emb_eq_one_iff, valuation_algebraMap_eq_one_iff hww₀]
  exact hc₄

omit [E.IsElliptic] in
include hww₀ hΔ in
/-- `‖Δ‖ < 1` over `K'_w` for a model `E` with `v_{w₀}(Δ(E)) < 1` at the place `w₀` below `w`. -/
lemma norm_Δ_curveLoc : ‖(curveLoc E K' w).Δ‖ < 1 := by
  rw [curveLoc, map_Δ, map_Δ, norm_emb_lt_one_iff, valuation_algebraMap_lt_one_iff hww₀]
  exact hΔ

omit [E.IsElliptic] in
include hww₀ hc₄ hΔ in
lemma norm_c₆_curveLoc : ‖(curveLoc E K' w).c₆‖ = 1 :=
  norm_c₆_eq_one _ (norm_c₄_curveLoc E hww₀ hc₄) (norm_Δ_curveLoc E hww₀ hΔ)

omit [E.IsElliptic] in
include hww₀ hc₄ hΔ in
lemma norm_d_curveLoc : ‖-((curveLoc E K' w).c₄ * (curveLoc E K' w).c₆)‖ = 1 := by
  rw [norm_neg, norm_mul, norm_c₄_curveLoc E hww₀ hc₄, norm_c₆_curveLoc E hww₀ hc₄ hΔ, one_mul]

end NormsAt

omit [E.IsElliptic] in
/-- `-(c₄c₆)` of `E` over `K'_w` is the image of the global `-(c₄c₆)`. -/
lemma neg_c₄_mul_c₆_curveLoc {K' : Type u} [Field K'] [NumberField K'] [Algebra F K']
    (w : FinitePlace K') :
    -((curveLoc E K' w).c₄ * (curveLoc E K' w).c₆) =
      FinitePlace.embedding w.maximalIdeal (algebraMap F K' (-(E.c₄ * E.c₆))) := by
  rw [curveLoc, map_c₄, map_c₄, map_c₆, map_c₆, map_neg, map_neg, map_mul, map_mul]

/-! ## The square root of `−c₄c₆` at a bad place -/

variable (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
  (hmult : ∀ v ∈ VBad, ∀ w : FinitePlace F, FinitePlace.LiesOver w v →
    HasMultiplicativeReductionAt E w)
  {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
  (TK : AddSubgroup (E.map (algebraMap F ↥K)).toAffine.Point)
  (hTK : TK ≤ AddSubgroup.torsionBy (E.map (algebraMap F ↥K)).toAffine.Point ℓ)
  (hcard : ℓ * ℓ ≤ Nat.card ↥TK)

include hℓ hodd hTK hcard in
set_option maxHeartbeats 1000000 in
-- the Galois-fixed-point and Hensel arguments over `K'_{w'}` and `K_w` are long
/-- **`−c₄c₆` is a square in `K_w`** for a model `E` with `v(c₄) = 1`, `v(Δ) < 1` at the place
of `F` below a place `w ∤ 2` of a field `K` over which `E` has `ℓ²` rational ℓ-torsion points. -/
theorem exists_sq_eq_neg_c₄_mul_c₆_of_valuation {w : FinitePlace ↥K}
    (h2w : (2 : 𝓞 ↥K) ∉ w.maximalIdeal.asIdeal)
    (hc₄ : (Tripod.placeUnder w : FinitePlace F).maximalIdeal.valuation F E.c₄ = 1)
    (hΔ : (Tripod.placeUnder w : FinitePlace F).maximalIdeal.valuation F E.Δ < 1) :
    ∃ s : localCompletion w,
      s ^ 2 = FinitePlace.embedding w.maximalIdeal (algebraMap F ↥K (-(E.c₄ * E.c₆))) := by
  set dK : ↥K := algebraMap F ↥K (-(E.c₄ * E.c₆)) with hdK
  by_cases hsq : IsSquare dK
  · obtain ⟨y, hy⟩ := exists_sq_eq_of_isSquare K hsq
    exact ⟨FinitePlace.embedding w.maximalIdeal y, by rw [← map_pow, hy]⟩
  -- the quadratic extension `K' = K(√d)`
  set K' := sqrtField K dK with hK'
  obtain ⟨w', hw'⟩ := FinitePlace.exists_liesOver (K := ↥K') w
  have hww₀ : FinitePlace.LiesOver w (Tripod.placeUnder w : FinitePlace F) := Tripod.liesOver_placeUnder w
  -- `2 ∉ w'`
  have h2w' : (2 : 𝓞 ↥K') ∉ w'.maximalIdeal.asIdeal := by
    haveI : w'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hw'
    intro h
    apply h2w
    rw [Ideal.mem_of_liesOver (P := w'.maximalIdeal.asIdeal), map_ofNat]
    exact h
  have h2L : ‖(2 : localCompletion w')‖ = 1 := norm_two_eq_one_of_notMem h2w'
  have h2L0 : (2 : localCompletion w') ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2L
    exact zero_ne_one h2L
  have h2K : ‖(2 : localCompletion w)‖ = 1 := norm_two_eq_one_of_notMem h2w
  -- the norm conditions over `L = K'_{w'}` and over `K_w`
  have hw'w₀ : FinitePlace.LiesOver w' (Tripod.placeUnder w : FinitePlace F) :=
    FinitePlace.liesOver_trans hw' hww₀
  have hc₄L := norm_c₄_curveLoc E (K' := ↥K') (w := w') hw'w₀ hc₄
  have hΔL := norm_Δ_curveLoc E (K' := ↥K') (w := w') hw'w₀ hΔ
  have hdL : ‖-((curveLoc E ↥K' w').c₄ * (curveLoc E ↥K' w').c₆)‖ = 1 :=
    norm_d_curveLoc E (w := w') hw'w₀ hc₄ hΔ
  have hdK1 : ‖FinitePlace.embedding w.maximalIdeal dK‖ = 1 := by
    have := norm_d_curveLoc E (K' := ↥K) (w := w) hww₀ hc₄ hΔ
    rwa [neg_c₄_mul_c₆_curveLoc] at this
  -- the square root `√d ∈ K'` and its image `s₀ ∈ L`
  set s₀ : localCompletion w' := FinitePlace.embedding w'.maximalIdeal (sqrtD K dK) with hs₀
  have hs₀sq : s₀ ^ 2 = -((curveLoc E ↥K' w').c₄ * (curveLoc E ↥K' w').c₆) := by
    rw [neg_c₄_mul_c₆_curveLoc, hs₀, ← map_pow, sqrtD_sq, IsScalarTower.algebraMap_apply F ↥K ↥K']
  have hs₀n : ‖s₀‖ = 1 := by
    have : ‖s₀‖ ^ 2 = 1 := by rw [← norm_pow, hs₀sq, hdL]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  -- `E` over `L` is a Tate curve
  have hc₄L0 : (curveLoc E ↥K' w').c₄ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc₄L
    exact zero_ne_one hc₄L
  obtain ⟨S⟩ : Nonempty (TateStructure (curveLoc E ↥K' w')) := by
    obtain ⟨t, C, hC, -⟩ := exists_variableChange_tateCurve h2L (twelve_ne_zero w')
      (curveLoc E ↥K' w') hc₄L hΔL (exists_tangent_root_of_sq _ h2L0 hc₄L0 hs₀sq)
    exact ⟨TateStructure.ofVariableChangeWithUniformization t C hC
      (uniformizeTateParameter t (twelve_ne_zero w') h2L)⟩
  -- the ℓ-torsion of `E(L)` is the image of `TK`
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI := S.finite_torsion ℓ
  let f : ↥TK → ↥(TateStructure.torsion ℓ (curveLoc E ↥K' w')) := fun R =>
    ⟨toLoc (k := ↥K) w' E R.1, by
      have h0 : ℓ • (R : (E.map (algebraMap F ↥K)).toAffine.Point) = 0 :=
        (AddSubgroup.torsionBy.nsmul_iff).mp (hTK R.2)
      rw [AddSubgroup.torsionBy.nsmul_iff, ← toLoc_nsmul]
      exact (congrArg (toLoc (k := ↥K) w' E) h0).trans (toLoc_zero w' E)⟩
  have hfinj : Function.Injective f := fun R R' h =>
    Subtype.ext (toLoc_injective (k := ↥K) w' E (congrArg Subtype.val h))
  have hcardL : ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ (curveLoc E ↥K' w')) :=
    hcard.trans (Nat.card_le_card_of_injective f hfinj)
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le ((S.card_torsion_le ℓ).trans hcard)
  by_cases hfix : galPlace (conj K hsq) w' = w'
  · -- the inert/ramified case is impossible
    exfalso
    set σ := localAut (conj K hsq) w' hfix with hσ
    have hE := map_curveLoc_localAut (conj K hsq) w' hfix E
    have htors : ∀ P ∈ TateStructure.torsion ℓ (curveLoc E ↥K' w'),
        pointMap (curveLoc E ↥K' w') (σ : localCompletion w' →+* localCompletion w') P =
          pointCongr hE.symm P := by
      intro P hP
      obtain ⟨R, hR⟩ := hfbij.2 ⟨P, hP⟩
      have hPR : P = toLoc (k := ↥K) w' E R.1 := (congrArg Subtype.val hR).symm
      rw [hPR]
      exact pointMap_localAut_toLoc (conj K hsq) w' hfix E R.1
    obtain ⟨r, hr, hr2⟩ := exists_sqrt_neg_c₄_mul_c₆_fixed σ (norm_localAut _ _ _)
      (curveLoc E ↥K' w') hE h2L (twelve_ne_zero w') S hℓ hodd htors hcardL
    have hσs₀ : σ s₀ = -s₀ := by
      rw [hs₀, hσ, localAut_embedding, conj_sqrtD, map_neg]
    have hrs : r = s₀ ∨ r = -s₀ := by
      rw [← hs₀sq] at hr2
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hr2
    have hs₀0 : s₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hs₀n
      exact zero_ne_one hs₀n
    rcases hrs with rfl | rfl
    · rw [hσs₀] at hr
      apply hs₀0
      have : (2 : localCompletion w') * s₀ = 0 := by linear_combination -hr
      exact (mul_eq_zero.mp this).resolve_left h2L0
    · rw [map_neg, hσs₀, neg_neg] at hr
      apply hs₀0
      have : (2 : localCompletion w') * s₀ = 0 := by linear_combination hr
      exact (mul_eq_zero.mp this).resolve_left h2L0
  · -- the split case: `√d` is congruent to an element of `𝓞_K` modulo `w'`
    have hgal : FinitePlace.LiesOver (galPlace (conj K hsq) w') w :=
      galPlace_liesOver (k₀ := ↥K) (fun _ => rfl) (conj K hsq) hw'
    have hf := inertiaDeg'_eq_one_of_ne (sqrtField_finrank_le K dK) (Ne.symm hfix) hw' hgal
    have hvs : w'.maximalIdeal.valuation ↥K' (sqrtD K dK) ≤ 1 := by
      rw [← norm_emb_le_one_iff, ← hs₀, hs₀n]
    obtain ⟨a, ha⟩ := exists_ringOfIntegers_sub_mem w' (sqrtD K dK) hvs
    obtain ⟨b, hb⟩ := exists_algebraMap_sub_mem_of_inertiaDeg_eq_one hw' hf a
    -- `w'(√d - b) < 1`
    have hb' : w'.maximalIdeal.valuation ↥K'
        (algebraMap (𝓞 ↥K') ↥K' (algebraMap (𝓞 ↥K) (𝓞 ↥K') b - a)) < 1 :=
      (valuation_lt_one_iff_mem _ _).mpr hb
    set bK : ↥K := algebraMap (𝓞 ↥K) ↥K b with hbK
    have hbK' : algebraMap ↥K ↥K' bK = algebraMap (𝓞 ↥K') ↥K' (algebraMap (𝓞 ↥K) (𝓞 ↥K') b) := by
      rw [hbK, ← IsScalarTower.algebraMap_apply (𝓞 ↥K) ↥K ↥K',
        IsScalarTower.algebraMap_apply (𝓞 ↥K) (𝓞 ↥K') ↥K']
    have hdiff : w'.maximalIdeal.valuation ↥K' (sqrtD K dK - algebraMap ↥K ↥K' bK) < 1 := by
      have : sqrtD K dK - algebraMap ↥K ↥K' bK =
          (sqrtD K dK - algebraMap (𝓞 ↥K') ↥K' a) -
            algebraMap (𝓞 ↥K') ↥K' (algebraMap (𝓞 ↥K) (𝓞 ↥K') b - a) := by
        rw [hbK', map_sub]
        ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt ha hb')
    -- `w'(d - b²) < 1`, hence `w(d - b²) < 1`
    have hsum : w'.maximalIdeal.valuation ↥K' (sqrtD K dK + algebraMap ↥K ↥K' bK) ≤ 1 := by
      refine (Valuation.map_add _ _ _).trans (max_le hvs ?_)
      rw [hbK']
      exact valuation_le_one w'.maximalIdeal (algebraMap (𝓞 ↥K) (𝓞 ↥K') b)
    have hdb : w'.maximalIdeal.valuation ↥K' (algebraMap ↥K ↥K' (dK - bK ^ 2)) < 1 := by
      have : algebraMap ↥K ↥K' (dK - bK ^ 2) =
          (sqrtD K dK - algebraMap ↥K ↥K' bK) * (sqrtD K dK + algebraMap ↥K ↥K' bK) := by
        rw [map_sub, map_pow, ← sqrtD_sq]
        ring
      rw [this, Valuation.map_mul]
      calc w'.maximalIdeal.valuation ↥K' (sqrtD K dK - algebraMap ↥K ↥K' bK) *
            w'.maximalIdeal.valuation ↥K' (sqrtD K dK + algebraMap ↥K ↥K' bK)
          ≤ w'.maximalIdeal.valuation ↥K' (sqrtD K dK - algebraMap ↥K ↥K' bK) * 1 :=
            mul_le_mul_right hsum _
        _ = w'.maximalIdeal.valuation ↥K' (sqrtD K dK - algebraMap ↥K ↥K' bK) := mul_one _
        _ < 1 := hdiff
    have hdbK : ‖FinitePlace.embedding w.maximalIdeal (dK - bK ^ 2)‖ < 1 := by
      rw [norm_emb_lt_one_iff, ← valuation_algebraMap_lt_one_iff hw']
      exact hdb
    -- Hensel in `K_w`
    have hbn : ‖FinitePlace.embedding w.maximalIdeal bK‖ = 1 := by
      have h1 : ‖(FinitePlace.embedding w.maximalIdeal bK) ^ 2‖ = 1 := by
        have : (FinitePlace.embedding w.maximalIdeal bK) ^ 2 =
            FinitePlace.embedding w.maximalIdeal dK -
              FinitePlace.embedding w.maximalIdeal (dK - bK ^ 2) := by
          rw [map_sub, map_pow]
          ring
        rw [this, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm,
          norm_neg, hdK1, max_eq_left hdbK.le]
        rw [norm_neg, hdK1]
        exact hdbK.ne'
      rw [norm_pow] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h1
    obtain ⟨s, hs, -⟩ := exists_sq_eq_of_norm_sq_sub_lt h2K hbn (a := FinitePlace.embedding w.maximalIdeal dK)
      (by rw [← map_pow, ← map_sub, ← neg_sub, map_neg, norm_neg]; exact hdbK)
    exact ⟨s, hs⟩

include hVBad hmult hℓ hodd hTK hcard in
/-- **`−c₄c₆` is a square in `K_w`** at every bad place `w` of a field `K` over which `E` has
`ℓ²` rational ℓ-torsion points. The valuation conditions hold for a model `C • E` at the place
of `F` below `w` (`AbcAdaptation.Reference.Iut.exists_variableChange_of_mult`); the ℓ-torsion of `C • E` over `K` is
transported from that of `E` along `AbcAdaptation.Reference.Iut.Anabelian.vcEquiv`, and a square root of
`−c₄c₆(C • E) = u⁻¹⁰ · (−c₄c₆(E))` gives one of `−c₄c₆(E)`. -/
theorem exists_sq_eq_neg_c₄_mul_c₆ {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) :
    ∃ s : localCompletion w,
      s ^ 2 = FinitePlace.embedding w.maximalIdeal (algebraMap F ↥K (-(E.c₄ * E.c₆))) := by
  obtain ⟨C, -, hc₄, hΔ⟩ := exists_variableChange_of_mult E _ (mult_placeUnder E K hmult hw)
  -- the ℓ-torsion of `C • E` over `K`
  set e : (E.map (algebraMap F ↥K)).toAffine.Point ≃+
      ((C • E).map (algebraMap F ↥K)).toAffine.Point :=
    (vcEquiv (C.map (algebraMap F ↥K)) (E.map (algebraMap F ↥K))).trans
      (pointCongr (map_variableChange (W := E) (C := C) (φ := algebraMap F ↥K))) with he
  set TK' : AddSubgroup ((C • E).map (algebraMap F ↥K)).toAffine.Point :=
    TK.map e.toAddMonoidHom with hTK'
  have hTK'le : TK' ≤ AddSubgroup.torsionBy ((C • E).map (algebraMap F ↥K)).toAffine.Point ℓ := by
    intro P hP
    obtain ⟨R, hR, rfl⟩ := AddSubgroup.mem_map.1 hP
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
      (AddSubgroup.torsionBy.nsmul_iff).1 (hTK hR), map_zero]
  have hcard' : ℓ * ℓ ≤ Nat.card ↥TK' :=
    hcard.trans (Nat.card_congr
      (AddSubgroup.equivMapOfInjective TK e.toAddMonoidHom e.injective).toEquiv).le
  obtain ⟨s', hs'⟩ := exists_sq_eq_neg_c₄_mul_c₆_of_valuation (C • E) K hℓ hodd TK' hTK'le hcard'
    (two_notMem_of_isBadPlace E K hVBad hw) hc₄ hΔ
  -- transport the square root along `u⁵`
  have h10 : ((C.u : F) * ((C.u⁻¹ : Fˣ) : F)) ^ 10 = 1 := by rw [C.u.mul_inv, one_pow]
  have hd : ((C.u : F) ^ 5) ^ 2 * (-((C • E).c₄ * (C • E).c₆)) = -(E.c₄ * E.c₆) := by
    rw [variableChange_c₄, variableChange_c₆]
    linear_combination (-(E.c₄ * E.c₆)) * h10
  refine ⟨FinitePlace.embedding w.maximalIdeal (algebraMap F ↥K ((C.u : F) ^ 5)) * s', ?_⟩
  rw [mul_pow, hs', ← map_pow, ← map_pow, ← map_mul, ← map_mul, hd]

end

end AbcAdaptation.Reference.Iut

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean (tateStructureOfTorsion)
-/

set_option autoImplicit false

open AbcAdaptation.Reference.Iut NumberField WeierstrassCurve
open scoped Classical Valued

universe u

/-- Full odd-prime torsion over an intermediate field gives a Tate structure at a bad place. -/
theorem solution
    {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
    {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
    (K : IntermediateField F Fbar) [NumberField ↥K]
    {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
    (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (TK : AddSubgroup (curveK E K).toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy (curveK E K).toAffine.Point ℓ)
    (hcard : ℓ * ℓ ≤ Nat.card ↥TK)
    {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) :
    Nonempty (TateStructure (curveKw E K w)) := by
  let pointGroup (d : DecidableEq ↥K) : AddCommGroup (curveK E K).toAffine.Point :=
    @Affine.Point.instAddCommGroup _ _ (curveK E K).toAffine d
  have square (d : DecidableEq ↥K)
      (T : @AddSubgroup _ (pointGroup d).toAddGroup)
      (hT : T ≤ @AddSubgroup.torsionBy _ (pointGroup d) ℓ)
      (hc : ℓ * ℓ ≤ Nat.card ↥T) :
      ∃ s : localCompletion w,
        s ^ 2 = FinitePlace.embedding w.maximalIdeal (algebraMap F ↥K (-(E.c₄ * E.c₆))) := by
    have hd : d = (fun a b => Classical.propDecidable (a = b)) :=
      funext fun a => funext fun b => Subsingleton.elim _ _
    subst d
    exact exists_sq_eq_neg_c₄_mul_c₆ E K hVBad hmult hℓ hodd T hT hc hw
  exact ⟨tateStructureOfBadPlace E K hVBad hmult hw
    (square inferInstance TK hTK hcard) uniformizeTateParameter⟩
