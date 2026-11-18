/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The iut contributors
-/
/-
Uncompiled draft: source declaration bodies selected byte-for-byte; wrappers and imports adapted.
Original repository: https://github.com/lana-agents/iut
Original revision recorded by existing adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
This draft does not itself establish accepted AST-command provenance.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open WeierstrassCurve NumberField
open scoped IntermediateField
variable (P : CurveProviders) (x : Pt)

/-- The tripodal field `F_tpd = ℚ(j, x(E_λ[2])) = ℚ(λ)` of the curve of `x`, as an intermediate
field of `F_λ`. -/
noncomputable abbrev tpd : IntermediateField ℚ (P.curve x).F :=
  tripodalFieldOf (P.curve x).F (P.curve x).E

/-- `λ` as an element of `F_λ = (P.curve x).F`. -/
noncomputable abbrev genC' : (P.curve x).F := genC x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)

/-- The curve of `x` is the Legendre curve of `λ`. -/
theorem curve_E_eq : (P.curve x).E = legendre (genC' P x) := rfl

instance : (legendre (genC' P x)).IsElliptic := (P.curve x).isElliptic

/-- `λ ∈ F_tpd`. -/
theorem genC_mem_tpd : genC' P x ∈ tpd P x := by
  change _ ∈ tripodalFieldOf (curveOf x _ _).F (curveOf x _ _).E
  rw [tripodalFieldOf_eq]
  exact IntermediateField.mem_adjoin_simple_self ℚ _

/-- `λ` as an element of `F_tpd`. -/
noncomputable def genT : tpd P x := ⟨_, genC_mem_tpd P x⟩

@[simp] theorem coe_genT : (genT P x : (P.curve x).F) = genC' P x := rfl

theorem algebraMap_genT : algebraMap (tpd P x) (P.curve x).F (genT P x) = genC' P x := rfl

/-- **`F_tpd ≃ ℚ(λ)`**: the tripodal field of `E_λ` inside `F_λ` is isomorphic to the minimal
field of definition `ℚ(λ) ⊆ ℚ̄` of `λ`. -/
noncomputable def tpdEquiv : tpd P x ≃ₐ[ℚ] fieldOf x.1 :=
  (IntermediateField.equivOfEq (tripodalFieldOf_eq x (P.torsionFinite3 x.1)
    (P.torsionFinite5 x.1))).trans (adjoinGenCEquiv x _ _)

theorem tpdEquiv_genT : tpdEquiv P x (genT P x) = gen x.1 := by
  apply Subtype.ext
  rfl

/-- `[F_tpd : ℚ] = deg λ`. -/
theorem finrank_tpd : Module.finrank ℚ (tpd P x) = deg x.1 := by
  rw [(tpdEquiv P x).toLinearEquiv.finrank_eq, deg_eq_finrank]

end AbcAdaptation.Tripod
