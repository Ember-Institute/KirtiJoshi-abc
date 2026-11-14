import Lean
import Definitions.Def_TripodNorthcottInputs
import Definitions.Def_TripodNorthcottComposition
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_norm_embedding_le_mulHeight_one
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_mulHeight_one_gen_le
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_coeff_minpoly_int_mem_Icc
import Theorems.Thm_AbcAdaptation_Tripod_northcottFiniteRoots
import Theorems.Thm_AbcAdaptation_Tripod_northcottPolynomialWitness
import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness
set_option autoImplicit false
open NumberField Polynomial
open scoped Classical
open AbcAdaptation
open AbcAdaptation.Tripod
open AbcAdaptation.Tripod.Northcott

section
theorem CompilerTarget_0 {K : Type*} [Field K] [NumberField K] (x : K)
    (φ : K →+* ℂ) : ‖φ x‖ ≤ Height.mulHeight₁ x := by sorry
end

section
theorem CompilerTarget_1 {d : ℕ} {H : ℝ} {x : Pt} (hd : x ∈ ptLE d) (hH : htCan x ≤ H) :
    Height.mulHeight₁ (gen x.1) ≤ heightBound d H := by sorry
end

section
theorem CompilerTarget_2 {K : Type*} [Field K] [NumberField K] {y : K}
    (hy : IsIntegral ℤ y) {d : ℕ} (hd : Module.finrank ℚ K ≤ d) {B : ℝ}
    (hB : ∀ φ : K →+* ℂ, ‖φ y‖ ≤ B) (i : ℕ) :
    (minpoly ℤ y).coeff i ∈ Set.Icc (-(coeffBoundOf d B : ℤ)) (coeffBoundOf d B) := by sorry
end

section
theorem CompilerTarget_3 : Northcott.FiniteRoots := by sorry
end

section
theorem CompilerTarget_4 : Northcott.PolynomialWitness := by sorry
end

section
theorem CompilerTarget_5 :
    AbcAdaptation.Tripod.BoundedDegreeFiniteness := by sorry
end

theorem PublishedExistingParent : AbcAdaptation.Tripod.BoundedDegreeFiniteness := by sorry
open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Northcott.norm_embedding_le_mulHeight_one
  let c ← getConstInfo `CompilerTarget_0
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Compiler formal differs Northcott.norm_embedding_le_mulHeight_one"
  let a ← getConstInfo `AbcAdaptation.Tripod.Northcott.mulHeight_one_gen_le
  let c ← getConstInfo `CompilerTarget_1
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Compiler formal differs Northcott.mulHeight_one_gen_le"
  let a ← getConstInfo `AbcAdaptation.Tripod.Northcott.coeff_minpoly_int_mem_Icc
  let c ← getConstInfo `CompilerTarget_2
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Compiler formal differs Northcott.coeff_minpoly_int_mem_Icc"
  let a ← getConstInfo `AbcAdaptation.Tripod.northcottFiniteRoots
  let c ← getConstInfo `CompilerTarget_3
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Compiler formal differs northcottFiniteRoots"
  let a ← getConstInfo `AbcAdaptation.Tripod.northcottPolynomialWitness
  let c ← getConstInfo `CompilerTarget_4
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Compiler formal differs northcottPolynomialWitness"
  let a ← getConstInfo `AbcAdaptation.Tripod.boundedDegreeFiniteness
  let c ← getConstInfo `CompilerTarget_5
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Compiler formal differs boundedDegreeFiniteness"
  let p ← getConstInfo `AbcAdaptation.Tripod.boundedDegreeFiniteness
  let q ← getConstInfo `PublishedExistingParent
  unless ← Lean.Meta.isDefEq p.type q.type do throwError "Published parent differs"
  IO.FS.writeFile ".local/adaptation/northcott-sourceproof-20261114/existing-types-equal.json" "true"
