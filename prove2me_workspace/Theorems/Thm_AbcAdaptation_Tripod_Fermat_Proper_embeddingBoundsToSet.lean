/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Solutions.Source_FermatEmbeddingBoundsSource

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem embeddingBoundsToSet {N : ℕ} (M : Model N)
    (hRF : ResiduesFinite M) : EmbeddingBoundsToSet M :=
  embeddingBoundsToSet_source M hRF

end AbcAdaptation.Tripod.Fermat.Proper
