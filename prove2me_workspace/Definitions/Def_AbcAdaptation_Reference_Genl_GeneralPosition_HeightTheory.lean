/- Adaptation draft: complete original HeightTheory structure and required source context. Original source notice retained. StatementI/II are omitted as separate source declarations. No target acceptance or publication is claimed. -/
/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference


universe u

namespace Genl

/-- An abstract height formalism in the sense of §1 of [mochizuki2010], containing the
data needed to state Theorem 2.1 of loc. cit.

A term `X : T.Curve` should be thought of as a pair `(X, D)` of a smooth, proper,
geometrically connected curve over a number field and a reduced effective divisor on it,
and `T.Pt X` as the set of algebraic points of `U_X = X \ D`. -/
structure HeightTheory where
  /-- The "curves" of the theory: pairs `(X, D)` of a smooth, proper, geometrically
  connected curve `X` over a number field and a reduced effective divisor `D ⊆ X`. -/
  Curve : Type u
  /-- The set of algebraic points `U_X(ℚ̄)` of `U_X = X \ D`. -/
  Pt : Curve → Type u
  /-- `U_X` is a hyperbolic curve, i.e. `deg ω_X(D) > 0`. -/
  Hyperbolic : Curve → Prop
  /-- The divisor `D` of the pair `(X, D)` is empty. -/
  DivisorFree : Curve → Prop
  /-- `ptLE X d` is the set `U_X(ℚ̄)^{≤d}` of points whose minimal field of definition
  has degree `≤ d` over `ℚ` (Example 1.3 (i) of [mochizuki2010]). -/
  ptLE : (X : Curve) → ℕ → Set (Pt X)
  /-- `ptEQ X d` is the set `U_X(ℚ̄)^{=d}` of points whose minimal field of definition
  has degree exactly `d` over `ℚ` (Example 1.3 (i) of [mochizuki2010]). -/
  ptEQ : (X : Curve) → ℕ → Set (Pt X)
  /-- There are no points of degree `≤ 0`. -/
  ptLE_zero : ∀ X, ptLE X 0 = ∅
  /-- `U_X(ℚ̄)^{≤ d + 1} = U_X(ℚ̄)^{≤ d} ∪ U_X(ℚ̄)^{= d + 1}`. -/
  ptLE_succ : ∀ X d, ptLE X (d + 1) = ptLE X d ∪ ptEQ X (d + 1)
  /-- A representative of the BD-class of height functions `ht_{ω_X(D)}` associated to
  the log canonical bundle `ω_X(D)` (Definition 1.2 (i), Proposition 1.4 (iii) of
  [mochizuki2010]). -/
  htCan : (X : Curve) → Pt X → ℝ
  /-- The log-different function `log-diff_X` (Definition 1.5 (iii) of
  [mochizuki2010]). -/
  logDiff : (X : Curve) → Pt X → ℝ
  /-- The log-conductor function `log-cond_D` (Definition 1.5 (iv) of
  [mochizuki2010]). -/
  logCond : (X : Curve) → Pt X → ℝ
  /-- The tripod `(ℙ¹_ℚ, {0, 1, ∞})`. -/
  tripod : Curve
  /-- The tripod is a hyperbolic curve. -/
  hyperbolic_tripod : Hyperbolic tripod
  /-- The collection of compactly bounded subsets `K_V ⊆ U_ℙ(ℚ̄)` whose support `V`
  contains the fixed finite set of primes `Σ` (Example 1.3 (ii) of [mochizuki2010]). -/
  CBS : Type u
  /-- The underlying set of algebraic points of a compactly bounded subset. -/
  cbsSet : CBS → Set (Pt tripod)

end Genl

end AbcAdaptation.Reference
