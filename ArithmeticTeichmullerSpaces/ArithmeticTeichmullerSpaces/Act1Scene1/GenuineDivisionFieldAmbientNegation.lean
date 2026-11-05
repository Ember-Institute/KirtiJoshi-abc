/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionFieldNegation
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.GenericPoint
import Mathlib.FieldTheory.Normal.Basic

/-!
source-id: JT-SCENE1-GENUINE-DIVISION-FIELD-AMBIENT-NEGATION-BOUNDARY
source: IUT I Definition 3.1(d); Mathlib `Normal` and the actual generic-point
transcendence theorem.
fidelity: records the exact obstruction to using `AlgEquiv.liftNormal` with
the constant field `k`: the ambient function-field closure contains the
transcendental generic x-coordinate, so the extension is not algebraic over k.
boundary: Scene1/Derived negative evidence. This file deliberately does not
introduce an ambient automorphism or a signed-group witness.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

theorem not_algebraic_functionFieldClosure_over_constants :
    ¬ Algebra.IsAlgebraic k (Ω E) := by
  intro h
  have hx : IsAlgebraic k (xG E) :=
    Algebra.IsAlgebraic.isAlgebraic (R := k) (xG E)
  exact (transcendental_xG E) hx

theorem not_normal_functionFieldClosure_over_constants :
    ¬ Normal k (Ω E) := by
  intro h
  exact not_algebraic_functionFieldClosure_over_constants E h.toIsAlgebraic

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
