/-
Adaptation provenance
Upstream repository https://github.com/lana-agents/tate-curves-theta
Revision ca6c2279d3cea0690cdb01328e727118d5485d68
Source declaration by Christian Merten in TateCurvesTheta/TateCurve/TatePointOnCurve.lean
TateCurvesTheta.TateParameter.tatePoint_mem'
-/
import TateCurvesTheta.TateCurve.TatePointOnCurve
import Solutions.Source_ReferenceIutTateUniformization

set_option autoImplicit false

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

open scoped Classical

variable {k : Type*} [NormedField k]

private def upstreamParameter (t : TateParameter k) : _root_.TateCurvesTheta.TateParameter k :=
  ⟨t.q, t.norm_lt_one⟩

variable [CompleteSpace k] [IsUltrametricDist k]

/-- The affine Tate coordinates satisfy the equation off the orbit of `q`. -/
theorem tatePoint_equation (t : TateParameter k) (h12 : (12 : k) ≠ 0) :
    t.TatePointEquation := by
  intro u hu
  exact _root_.TateCurvesTheta.TateParameter.tatePoint_mem' (upstreamParameter t) h12 hu

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter
