/- Adaptation from exact original source commands. The original epsilonE and deltaBound definition bodies are retained. The source-generated epsilonE.eq_1 equation is proved by reflexivity. Original notice retained below. -/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Defs

namespace AbcAdaptation.Reference


set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v w

open Finset Real

/-- The tolerance `ε_E = (60δ)²·log(2δh)/√h` of Corollary 2.2(ii). -/
noncomputable def epsilonE (δ h : ℝ) : ℝ :=
  (60 * δ) ^ 2 * Real.log (2 * δ * h) / Real.sqrt h

/-- `δ = 2¹²·3³·5·d = 552960·d`, the bound on `[F : ℚ]` for the Θ-data field of a point of degree
`≤ d` ((E3)–(E5) in the proof of Theorem 1.10). -/
noncomputable def deltaBound (d : ℕ) : ℝ := 552960 * (d : ℝ)

-- Preserve the source API by materializing the compiler's lazy equation.
attribute [local simp] epsilonE.eq_1

end Iut

end AbcAdaptation.Reference
