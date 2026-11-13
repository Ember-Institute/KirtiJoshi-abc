/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent statement adaptation of Iut/Tripod/Height.lean and
Iut/Implication/Corollary22.lean. No Iut or Genl module is imported.
-/
import Definitions.Def_TripodStatementIIInputs

set_option autoImplicit false

open NumberField

namespace AbcAdaptation.Tripod

/-- The finite part of Mathlib's relative number-field logarithmic height.
This is the exact expression called `Iut.finHeight` in the source. -/
noncomputable def finHeight {F : Type*} [Field F] [NumberField F] (y : F) : ℝ :=
  ∑ᶠ v : FinitePlace F, Real.posLog (v y)

/-- The actual Legendre `j`-invariant, with the source's factor `256`. -/
noncomputable def legendreJ {F : Type*} [Field F] (z : F) : F :=
  256 * (z ^ 2 - z + 1) ^ 3 / (z ^ 2 * (z - 1) ^ 2)

/-- The canonical auxiliary elliptic height, computed in the actual field
`ℚ(x)`. Source `h_eq_finHeight_div` identifies this exact expression with
`log(q_∀(E_x))`; it is not a freely chosen height function. -/
noncomputable def auxiliaryHeight (x : Pt) : ℝ :=
  finHeight (legendreJ (gen x.1)) / deg x.1

/-- The exact numeric degree-bound expression from Corollary 2.2. -/
noncomputable def deltaBound (d : ℕ) : ℝ := 552960 * (d : ℝ)

/-- The exact Corollary 2.2 error function, including its square-root
denominator and the logarithm's factor `2`. -/
noncomputable def epsilonE (δ h : ℝ) : ℝ :=
  (60 * δ) ^ 2 * Real.log (2 * δ * h) / Real.sqrt h

/-- Open child: on each actual compactly bounded set, the canonical
auxiliary height divided by `6` has uniformly bounded discrepancy from the
existing `htCan`. This is a consequence of the two bounds in source
`legendreHeight`, after `h_eq_finHeight_div`; no degree bound is added. -/
def CanonicalLegendreHeightComparison : Prop :=
  ∀ K : CompactlyBounded, ∃ B : ℝ,
    ∀ x : Pt, x ∈ K.set → |auxiliaryHeight x / 6 - htCan x| ≤ B

/-- Open child: the full Corollary 2.2 high-height conclusion for the fixed
canonical height. The finite set can be the intersection of source
`excCore` with `K.set ∩ ptLE d`, which is the source's finiteness scope.
`H` and `C` are uniform in `x`, with source values `I.threshold cheb` and
`40 * pnt.η + I.B / 3`. This is a consequence schema for concrete tripod
data, not the source theorem's polymorphic input-bundle type. -/
def CanonicalCorollary22HighHeightEstimate : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ K : CompactlyBounded,
    ∃ (E : Set Pt) (H C : ℝ), E.Finite ∧
      ∀ x : Pt, x ∈ K.set → deg x.1 ≤ d → x ∉ E → H ≤ auxiliaryHeight x →
        (1 / 6 : ℝ) * auxiliaryHeight x ≤
            (1 + epsilonE (deltaBound d) (auxiliaryHeight x)) *
              (logDiff x + logCond x) + C ∧
          epsilonE (deltaBound d) (auxiliaryHeight x) ≤ 1 ∧
          0 ≤ logDiff x + logCond x

/-- Open numeric child: the exact real-variable statement of source
`epsilonE_le`, with its fourth-power threshold and separate `1 ≤ h`
hypothesis. It does not assert a rate for an arbitrary error function. -/
def EpsilonELargeHeight : Prop :=
  ∀ (δ h ε : ℝ), 1 ≤ δ → 0 < ε →
    ((60 * δ) ^ 2 * (2 * δ + 4) / ε) ^ 4 ≤ h → 1 ≤ h →
      epsilonE δ h ≤ ε

end AbcAdaptation.Tripod
