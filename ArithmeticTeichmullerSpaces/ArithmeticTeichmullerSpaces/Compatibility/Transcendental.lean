/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

original-path: Mathlib/RingTheory/Algebraic/Basic.lean
original-commit: 389347a7c1cfa76f6bd5be2ca35d4cb621610ad3
license-review: Apache-2.0 header and repository LICENSE reviewed before copying.
modifications: copy only Transcendental.ne_zero into the project namespace.
-/
import Mathlib.RingTheory.Algebraic.Basic

namespace JoshiTeich.Compatibility

@[grind →]
theorem transcendental_ne_zero {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [Nontrivial R] {x : A} (ht : Transcendental R x) : x ≠ 0 :=
  fun h ↦ ht (h ▸ isAlgebraic_zero)

end JoshiTeich.Compatibility
