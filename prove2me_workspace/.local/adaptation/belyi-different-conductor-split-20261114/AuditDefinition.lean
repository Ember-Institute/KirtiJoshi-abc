import Lean
import Definitions.Def_FermatBelyiDifferentConductorChildren
import Definitions.Def_FermatBelyiComparisons
import Mathlib.NumberTheory.NumberField.Discriminant.Different

open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; validation and source mappings are recorded with this unit.
-/

set_option autoImplicit false
open NumberField
open scoped Classical IntermediateField

namespace PlatformDefinitionAudit

/-- Exactly Heights.Different.cond, with the finite-place norm expanded. -/
noncomputable def finiteSetLogCond {F : Type*} [Field F] [NumberField F]
    (S : Finset F) : ℝ :=
  (∑ᶠ w : FinitePlace F,
    if ∃ a ∈ S, 1 < w a then Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0) /
      Module.finrank ℚ F

noncomputable def tripodConductorGenerators (y : Tripod.Pt) :
    Finset (Tripod.fieldOf y.1) :=
  {Tripod.gen y.1, (Tripod.gen y.1)⁻¹, (1 - Tripod.gen y.1)⁻¹}

noncomputable def evaluatedCuspGenerators {N : ℕ} {M : Model N}
    (x : QbarPoint M.K) (G : Finset M.K) (hG : ∀ g ∈ G, g ∈ x.P.1) :
    Finset x.fieldOf :=
  G.attach.image (fun g => evalInPointField x g.1 (hG g.1 g.2))

/-- The actual image-field inclusion fixes the algebra used by the relative different.
The denominator is the full residue-image field degree. -/
noncomputable def belyiRelativeLogDifferent {N : ℕ} (M : Model N)
    (hRF : ResiduesFinite M) (φ : M.K) (x : QbarPoint M.K)
    (hgood : GoodValue M x φ) : ℝ := by
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
    (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
  exact Real.log (Ideal.absNorm
    (differentIdeal (𝓞 (Tripod.fieldOf (belyiImage M φ x).1)) (𝓞 x.fieldOf))) /
      x.degree

/-- Source numeric child: no curve field, height, or number field is supplied freely.
Both fields are fixed by the actual x and actual φ(x). S,T are actual finite element sets. -/
def BelyiActualFieldConductorExtension : Prop :=
  ∀ {N : ℕ} (M : Model N) (hRF : ResiduesFinite M) (φ : M.K)
    (x : QbarPoint M.K) (hgood : GoodValue M x φ),
    letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
    ∀ (S : Finset (Tripod.fieldOf (belyiImage M φ x).1)) (T : Finset x.fieldOf),
      S.image (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)) ⊆ T →
      finiteSetLogCond S ≤ finiteSetLogCond T +
        belyiRelativeLogDifferent M hRF φ x hgood

/-- The actual full-field different tower identity. Image and point degrees stay distinct. -/
def BelyiActualFieldDifferentTower : Prop :=
  ∀ {N : ℕ} (M : Model N) (hRF : ResiduesFinite M) (φ : M.K)
    (x : QbarPoint M.K) (hgood : GoodValue M x φ),
      pointLogDiff M hRF x = Tripod.logDiff (belyiImage M φ x) +
        belyiRelativeLogDifferent M hRF φ x hgood

/-- Numeric identification for the three actual tripod generators. -/
def TripodGeneratorConductorIdentity : Prop :=
  ∀ y : Tripod.Pt, Tripod.logCond y = finiteSetLogCond (tripodConductorGenerators y)

end PlatformDefinitionAudit

open Lean
run_meta do
  let pairs : Array (Name × Name) := #[(`AbcAdaptation.Tripod.Fermat.Proper.finiteSetLogCond, `PlatformDefinitionAudit.finiteSetLogCond),(`AbcAdaptation.Tripod.Fermat.Proper.tripodConductorGenerators, `PlatformDefinitionAudit.tripodConductorGenerators),(`AbcAdaptation.Tripod.Fermat.Proper.evaluatedCuspGenerators, `PlatformDefinitionAudit.evaluatedCuspGenerators),(`AbcAdaptation.Tripod.Fermat.Proper.belyiRelativeLogDifferent, `PlatformDefinitionAudit.belyiRelativeLogDifferent),(`AbcAdaptation.Tripod.Fermat.Proper.BelyiActualFieldConductorExtension, `PlatformDefinitionAudit.BelyiActualFieldConductorExtension),(`AbcAdaptation.Tripod.Fermat.Proper.BelyiActualFieldDifferentTower, `PlatformDefinitionAudit.BelyiActualFieldDifferentTower),(`AbcAdaptation.Tripod.Fermat.Proper.TripodGeneratorConductorIdentity, `PlatformDefinitionAudit.TripodGeneratorConductorIdentity)]
  let mut rows : Array Json := #[]
  for (original, uploaded) in pairs do
    let a ← getConstInfo original
    let c ← getConstInfo uploaded
    unless ← Meta.isDefEq a.type c.type do throwError "Definition type differs: {original}"
    let aExpr ← Meta.mkConstWithFreshMVarLevels original
    let cExpr ← Meta.mkConstWithFreshMVarLevels uploaded
    unless ← Meta.withTransparency .all (Meta.isDefEq aExpr cExpr) do
      throwError "Definition body differs: {original}"
    let axs ← collectAxioms uploaded
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected definition axiom {ax}"
    rows := rows.push (Json.mkObj [("name",toJson original.toString),
      ("type_equal",Json.bool true),("body_equal",Json.bool true),
      ("axioms",toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/belyi-different-conductor-split-20261114/definition-type-audit.json" (Json.pretty (Json.arr rows))
