/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Source: Genl/Mathlib/Order/BoundedDiscrepancy.lean:141 at pinned Genl
 ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf. Exact ge proof body.
-/
import Definitions.Def_AbcAdaptation_Reference_Genl_Mathlib_Order_BoundedDiscrepancy

namespace AbcAdaptation.Reference

variable {α : Type*}

namespace DiscrepancyEquiv

variable {f g : α → ℝ} {s : Set α}

theorem ge (hfg : f ≈[s] g) : g ≲[s] f := hfg.2

end DiscrepancyEquiv
end AbcAdaptation.Reference
