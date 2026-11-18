/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly

namespace AbcAdaptation.Tripod.CurveProviders

open AbcAdaptation.Reference.Iut

variable (P : CurveProviders)

/-- The Tate inputs of `E_λ`. -/
noncomputable def tate (x : Pt) : (P.curve x).TateInputs := (P.curve x).tateInputs

/-- The local height data of `E_λ`. -/
noncomputable def localData (x : Pt) : LocalHeightData :=
  (P.curve x).localHeightData (P.arith x) (P.tate x)

/-- The height `h(λ) = log(q_∀(E_λ))`. -/
noncomputable def h (x : Pt) : ℝ := (P.localData x).height

end AbcAdaptation.Tripod.CurveProviders
