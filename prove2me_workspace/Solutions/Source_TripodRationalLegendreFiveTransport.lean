import Solutions.Source_TripodRationalLegendreFive
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_JTransport
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-- The rational Legendre parameter realized in the actual tripod. -/
noncomputable def rationalLegendreFivePoint (m : ℕ) : Pt :=
  rationalPoint (rationalLegendreFiveParam m)
    (ne_of_gt (by linarith [(rationalLegendreFiveParam_bounds m).1]))
    (ne_of_lt (by linarith [(rationalLegendreFiveParam_bounds m).2]))

theorem rationalLegendreFivePoint_deg (m : ℕ) :
    deg (rationalLegendreFivePoint m).1 = 1 := by
  rw [deg_eq_finrank]
  have hfield : fieldOf (rationalLegendreFivePoint m).1 = ⊥ :=
    IntermediateField.adjoin_simple_eq_bot_iff.mpr
      (IntermediateField.mem_bot.mpr ⟨rationalLegendreFiveParam m, rfl⟩)
  rw [hfield, IntermediateField.finrank_bot]

/-- The provider's actual curve has the image of the rational Legendre invariant. -/
theorem curve_j_rationalLegendreFivePoint (P : CurveProviders) (m : ℕ) :
    (P.curve (rationalLegendreFivePoint m)).E.j =
      algebraMap ℚ (P.curve (rationalLegendreFivePoint m)).F
        (legendreJ (rationalLegendreFiveParam m)) := by
  let x := rationalLegendreFivePoint m
  let F := (P.curve x).F
  let f : F →ₐ[ℚ] Qbar := embC x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)
  have hx : f (genC' P x) = algebraMap ℚ Qbar (rationalLegendreFiveParam m) := rfl
  change (P.curve x).E.j = algebraMap ℚ F (legendreJ (rationalLegendreFiveParam m))
  apply f.injective
  calc
    f (P.curve x).E.j = f (legendreJ (genC' P x)) :=
      f.congr_arg (curve_j_eq_legendreJ P x)
    _ = legendreJ (f (genC' P x)) := map_legendreJ f.toRingHom (genC' P x)
    _ = legendreJ (algebraMap ℚ Qbar (rationalLegendreFiveParam m)) := congrArg legendreJ hx
    _ = algebraMap ℚ Qbar (legendreJ (rationalLegendreFiveParam m)) :=
      (map_legendreJ (algebraMap ℚ Qbar) (rationalLegendreFiveParam m)).symm
    _ = f (algebraMap ℚ F (legendreJ (rationalLegendreFiveParam m))) := (f.commutes _).symm

end AbcAdaptation.Tripod
