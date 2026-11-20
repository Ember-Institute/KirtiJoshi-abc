/-
Adaptation provenance
Upstream repository https://github.com/lana-agents/tate-curves-theta
Revision ca6c2279d3cea0690cdb01328e727118d5485d68
Source declarations by Christian Merten in TateCurvesTheta.TateParameter
  TateCurvesTheta/TateCurve/TatePointOnCurve.lean, tatePoint_mem'
  TateCurvesTheta/TateCurve/GroupLaw.lean, tatePoint_mul
  TateCurvesTheta/TateCurve/TateUniformization.lean, tatePoint_surjective
The bridge uses the same parameter, Weierstrass model, and coordinate series
in both namespaces. The point maps agree by proof irrelevance.
-/
import TateCurvesTheta.TateCurve.TateUniformization
import Solutions.Source_ReferenceIutTatePointEquation

set_option autoImplicit false

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

open scoped Classical

variable {k : Type*} [NormedField k]

private def upstreamParameter (t : TateParameter k) : _root_.TateCurvesTheta.TateParameter k :=
  ⟨t.q, t.norm_lt_one⟩

variable [CompleteSpace k] [IsUltrametricDist k]

private theorem tatePoint_eq_upstream (t : TateParameter k) (hmem : t.TatePointEquation)
    (h12 : (12 : k) ≠ 0) (h2 : ‖(2 : k)‖ = 1) (u : kˣ) :
    t.tatePoint hmem h12 u =
      _root_.TateCurvesTheta.TateParameter.tatePoint (upstreamParameter t) hmem ⟨h2, h12⟩ u :=
  rfl

/-- The Tate point map sends multiplication of units to addition of curve points. -/
theorem tatePoint_mul [DecidableEq k] (t : TateParameter k) (hmem : t.TatePointEquation)
    (h12 : (12 : k) ≠ 0) (h2 : ‖(2 : k)‖ = 1) (u v : kˣ) :
    t.tatePoint hmem h12 (u * v) = t.tatePoint hmem h12 u + t.tatePoint hmem h12 v := by
  rw [tatePoint_eq_upstream t hmem h12 h2, tatePoint_eq_upstream t hmem h12 h2 u,
    tatePoint_eq_upstream t hmem h12 h2 v]
  exact _root_.TateCurvesTheta.TateParameter.tatePoint_mul (upstreamParameter t) hmem ⟨h2, h12⟩ u v

/-- Every point on the Tate curve is the image of a unit. -/
theorem tatePoint_surjective (t : TateParameter k) (hmem : t.TatePointEquation)
    (h12 : (12 : k) ≠ 0) (h2 : ‖(2 : k)‖ = 1) :
    Function.Surjective (t.tatePoint hmem h12) := by
  intro P
  obtain ⟨u, hu⟩ := _root_.TateCurvesTheta.TateParameter.tatePoint_surjective
    (upstreamParameter t) hmem ⟨h2, h12⟩ P
  exact ⟨u, (tatePoint_eq_upstream t hmem h12 h2 u).trans hu⟩

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter

namespace AbcAdaptation.Reference.Iut

open AbcAdaptation.Reference.TateCurvesTheta
open scoped Classical

variable {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]

/-- The Tate parameter gives a uniformization over a complete field of odd residue characteristic. -/
noncomputable def TateParameterUniformization.ofTateParameter
    (t : TateParameter k) (h12 : (12 : k) ≠ 0) (h2 : ‖(2 : k)‖ = 1) :
    TateParameterUniformization t :=
  let hmem := t.tatePoint_equation h12
  TateParameterUniformization.ofTatePoint t hmem h12
    (t.tatePoint_mul hmem h12 h2) (t.tatePoint_surjective hmem h12 h2)

end AbcAdaptation.Reference.Iut
