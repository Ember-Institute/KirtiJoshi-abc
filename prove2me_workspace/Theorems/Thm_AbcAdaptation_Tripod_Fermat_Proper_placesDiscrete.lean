/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatCurveFieldResidue

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem placesDiscrete {N : ℕ} (M : Model N) : PlacesDiscrete M :=
  model_placesDiscrete M

end AbcAdaptation.Tripod.Fermat.Proper
