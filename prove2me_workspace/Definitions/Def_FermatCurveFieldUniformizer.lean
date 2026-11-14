/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of complete pinned Belyi source proofs.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
See source-consumer.json for source spans and actual consumers.
Source: Belyi/CurveField/Extension.lean; SHA-256: 690dcc66979c9da2c21c1b765ce6d53eb41e5e850a71e42de91fa8ffc3839ddb.
-/
import Definitions.Def_FermatCurveFieldPlace

set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.Place

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

noncomputable def uniformizer (P : Place K) : K := Classical.choose P.exists_ord_eq_one



end AbcAdaptation.Tripod.Fermat.Proper.Place
