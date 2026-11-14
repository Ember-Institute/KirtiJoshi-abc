import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalCuspPolarLinearEquivalence
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_polarPresentationHeightSum_of_principalRelation
/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors

Independent adaptation of Genl/Curves/BelyiDescent.lean:215 at
ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf. Both exact mathematical
child inputs below remain separate open theorem obligations.
-/
import Definitions.Def_FermatBelyiComparisons

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The good-open value has precisely the existing tripod height.
This identity uses the actual minimal field of φ(x); it adds no error term. -/
theorem functionHeight_eq_htCan_belyiImage {N : ℕ}
    (M : Model N) (φ : M.K) (x : QbarPoint M.K) (hgood : GoodValue M x φ) :
    functionHeight M φ x = Tripod.htCan (belyiImage M φ x) := by
  obtain ⟨hφ, h0, h1⟩ := hgood
  rw [functionHeight_of_regular M φ x hφ, belyiImage_eq M φ x hφ h0 h1]
  rfl

/-- The original comparison follows from the actual divisor coefficient
relation and the general height comparison for every explicit presentation. -/
theorem belyiHeightRelation_of_children
    (hGeometry : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
      (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ)
      (hfin : (cusps M hDVR φ).Finite) (K : CanonicalDivisorData M hDVR),
      ∃ r : M.K, r ≠ 0 ∧ ∀ P : Place M.K,
        K.D P + cuspDivisor M hDVR φ hfin P =
          poleMultiplicity M hDVR φ P + ord M hDVR P r)
    (hPolarHeights : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
      (hRF : ResiduesFinite M) (D E : Divisor M)
      (RD : PolarPresentation M hDVR D) (RE : PolarPresentation M hDVR E)
      (f r : M.K) (hr : r ≠ 0)
      (hrel : ∀ P : Place M.K,
        D P + E P = poleMultiplicity M hDVR f P + ord M hDVR P r),
      ∃ C : ℝ, ∀ x : QbarPoint M.K,
        |divHeight RD x + divHeight RE x - functionHeight M f x| ≤ C) :
    BelyiHeightRelation := by
  intro N M hDVR hRF A φ hφ hfin B
  obtain ⟨r, hr, hrel⟩ := hGeometry M hDVR hRF φ hφ hfin B.canonical
  obtain ⟨C, hC⟩ := hPolarHeights M hDVR hRF
    B.canonical.D (cuspDivisor M hDVR φ hfin)
    B.canonicalPresentation B.cuspPresentation φ r hr hrel
  refine ⟨C, ?_⟩
  intro p hgood
  rw [← functionHeight_eq_htCan_belyiImage M φ (affineLift M A p) hgood]
  exact hC (affineLift M A p)

end AbcAdaptation.Tripod.Fermat.Proper

theorem solution : AbcAdaptation.Tripod.Fermat.Proper.BelyiHeightRelation :=
  AbcAdaptation.Tripod.Fermat.Proper.belyiHeightRelation_of_children
    AbcAdaptation.Tripod.Fermat.Proper.canonicalCuspPolarLinearEquivalence
    AbcAdaptation.Tripod.Fermat.Proper.polarPresentationHeightSum_of_principalRelation

theorem PlatformOriginalParentType : AbcAdaptation.Tripod.Fermat.Proper.BelyiHeightRelation := solution

theorem PlatformChildType0 : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    ∀ (φ : ↥M.K),
      AbcAdaptation.Tripod.Fermat.Proper.IsBelyi M hDVR φ →
        ∀ (hfin : (AbcAdaptation.Tripod.Fermat.Proper.cusps M hDVR φ).Finite)
          (K : AbcAdaptation.Tripod.Fermat.Proper.CanonicalDivisorData M hDVR),
          ∃ (r : ↥M.K),
            r ≠ 0 ∧
              ∀ (P : AbcAdaptation.Tripod.Fermat.Proper.Place ↥M.K),
                K.D P + (AbcAdaptation.Tripod.Fermat.Proper.cuspDivisor M hDVR φ hfin) P =
                  AbcAdaptation.Tripod.Fermat.Proper.poleMultiplicity M hDVR φ P +
                    AbcAdaptation.Tripod.Fermat.Proper.ord M hDVR P r := AbcAdaptation.Tripod.Fermat.Proper.canonicalCuspPolarLinearEquivalence

theorem PlatformChildType1 : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    ∀ (D E : AbcAdaptation.Tripod.Fermat.Proper.Divisor M)
      (RD : AbcAdaptation.Tripod.Fermat.Proper.PolarPresentation M hDVR D)
      (RE : AbcAdaptation.Tripod.Fermat.Proper.PolarPresentation M hDVR E) (f r : ↥M.K),
      r ≠ 0 →
        (∀ (P : AbcAdaptation.Tripod.Fermat.Proper.Place ↥M.K),
            D P + E P =
              AbcAdaptation.Tripod.Fermat.Proper.poleMultiplicity M hDVR f P +
                AbcAdaptation.Tripod.Fermat.Proper.ord M hDVR P r) →
          ∃ (C : ℝ),
            ∀ (x : AbcAdaptation.Tripod.Fermat.Proper.QbarPoint ↥M.K),
              |AbcAdaptation.Tripod.Fermat.Proper.divHeight RD x + AbcAdaptation.Tripod.Fermat.Proper.divHeight RE x -
                    AbcAdaptation.Tripod.Fermat.Proper.functionHeight M f x| ≤
                C := AbcAdaptation.Tripod.Fermat.Proper.polarPresentationHeightSum_of_principalRelation

open Lean
run_meta do
  let original ← getConstInfo `PlatformOriginalParentType
  let solution ← getConstInfo `solution
  unless ← Lean.Meta.isDefEq original.type solution.type do throwError "Original parent type differs"
  let axs ← collectAxioms `solution
  unless axs.contains `sorryAx do throwError "Missing expected open child dependency"
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains ax do throwError "Unexpected reduction axiom {ax}"
  let pairs : Array (Name × Name) := #[(`AbcAdaptation.Tripod.Fermat.Proper.canonicalCuspPolarLinearEquivalence, `PlatformChildType0),(`AbcAdaptation.Tripod.Fermat.Proper.polarPresentationHeightSum_of_principalRelation, `PlatformChildType1)]
  let mut rows : Array Json := #[]
  for (name, check) in pairs do
    let a ← getConstInfo name
    let t ← getConstInfo check
    unless ← Lean.Meta.isDefEq a.type t.type do throwError "Uploaded child type differs: {name}"
    rows := rows.push (Json.mkObj [("name",toJson name.toString),("type",Json.str (← Lean.Meta.ppExpr a.type).pretty)])
  IO.FS.writeFile ".local/adaptation/belyi-height-split-20261114/type-audit.json" (Json.pretty (Json.mkObj [("original_parent_type_equal",Json.bool true),("solution_type",Json.str (← Lean.Meta.ppExpr solution.type).pretty),("axioms",toJson (axs.map toString)),("child_types",Json.arr rows)]))
