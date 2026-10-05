import ArithmeticTeichmullerSpaces.Act1Scene1.Boundary
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: JT-ATS-III-COR312-TARGET
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
  `cor:cor312`, lines 3647-3650; preceding volume form `th:moccor-Mochizuki-form2`,
  lines 3617-3632
fidelity: exact analytic inequality shape; the theta-volume realization and the
  finite `(p,w)` q-term index are explicit Scene1 data and remain to be derived
  from the Prologue inputs.
boundary: Scene1/Derived; this declaration is not part of Prologue/Core.

This file fixes the target proposition before the Scene1 proof is attempted.  It
does not assert that the target-specific volume or q-terms can already be built.
-/

structure Corollary312Data
    (K : Type uK) [Field K] [NumberField K]
    (O : Type uK) [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O] where
  scene1 : Scene1Input K O p
  ell : ℕ
  ellStar : ℕ
  qIndex : Type uK
  qIndexFintype : Fintype qIndex
  qLogTerm : qIndex → ℝ
  thetaVolume : ℝ

namespace Corollary312Data

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

def qLogSum (T : Corollary312Data K O p) : ℝ :=
  letI := T.qIndexFintype
  ∑ i, T.qLogTerm i

def qProduct (T : Corollary312Data K O p) (qFactor : T.qIndex → ℝ) : ℝ :=
  letI := T.qIndexFintype
  ∏ i, qFactor i ^ T.ellStar

end Corollary312Data

/-!
The source's `qLogTerm` records the flattened finite sum over the pairs `(p,w)`
with `w ∈ 𝕍_p^oss`.  The flattening is a target-specific representation choice;
the boundary audit must later record the construction that identifies it with the
paper's indexed family.
-/
def Corollary312
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) : Prop :=
  -(1 / (T.ellStar : ℝ)) * |Real.log T.thetaVolume| ≥
    -Corollary312Data.qLogSum p T

/-! These are source-side side conditions, kept separate from the target inequality. -/
structure Corollary312SideConditions
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) : Prop where
  ell_prime : Nat.Prime T.ell
  ell_ge_five : 5 ≤ T.ell
  ellStar_eq_half_sub_one : T.ellStar = (T.ell - 1) / 2
  ellStar_pos : 0 < T.ellStar
  thetaVolume_pos : 0 < T.thetaVolume

end JoshiTeich.Act1Scene1
