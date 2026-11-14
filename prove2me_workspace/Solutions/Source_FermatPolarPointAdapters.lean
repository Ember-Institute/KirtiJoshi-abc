/-
Independent source-proof adaptation; validation is recorded in this unit's CI receipts.
Only adapters to existing proved point/order APIs; no new open obligation.
Belyi/CurveField/Point.lean at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8
is the reference for the zero-inclusive evaluation statement.
-/
import Definitions.Def_FermatNoncriticalElementarySource
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper
namespace QbarPoint

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- Uses the already proved finite residue field, without shrinking the point field. -/
instance polar_finiteDimensional_fieldOf (x : QbarPoint K) :
    FiniteDimensional ℚ x.fieldOf :=
  x.σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional

/-- Zero-inclusive wrapper around the existing nonzero evaluation theorem. -/
theorem polar_eval_eq_zero_iff' (x : QbarPoint K) {f : K} (hf : f ∈ x.P.1) :
    x.eval f hf = 0 ↔ f = 0 ∨ 0 < x.P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp only [noncritical_eval_zero, true_or, iff_self]
  · simp only [hf0, false_or, x.noncritical_eval_zero_iff hf hf0]

end QbarPoint
end AbcAdaptation.Tripod.Fermat.Proper
