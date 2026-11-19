/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/Residual.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants
import Solutions.Source_TripodPlaceUnder
import Solutions.Source_TripodRelativeDegreeTower
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField

universe u

/-- **The wild constants** `c_p` of the different bound: the `p`-adic valuation of
`2¹²·3²·5` (the degree `[F : F_tpd]`) plus `1` at `p = ℓ`. -/
def wildConst (ℓ p : ℕ) : ℕ :=
  (if p = 2 then 12 else if p = 3 then 2 else if p = 5 then 1 else 0) + (if p = ℓ then 1 else 0)

lemma wildConst_eq_zero {ℓ p : ℕ} (hp : p ∉ ({2, 3, 5, ℓ} : Finset ℕ)) : wildConst ℓ p = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  simp [wildConst, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

/-! ### The tower of fields -/

section Fields

variable (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

/-- `F_mod = ℚ(j) ⊆ F_tpd = ℚ(j, x(E[2]))`. -/
lemma fieldOfModuli_le_tripodalFieldOf : fieldOfModuli F E ≤ tripodalFieldOf F E :=
  IntermediateField.adjoin_simple_le_iff.mpr
    (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _))

/-- The `F_mod`-algebra structure of `F_tpd`, by the inclusion. -/
noncomputable instance instAlgebraFieldOfModuliTripodal :
    Algebra ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) :=
  (IntermediateField.inclusion (fieldOfModuli_le_tripodalFieldOf F E)).toAlgebra

lemma algebraMap_fieldOfModuli_tripodal_apply (x : ↥(fieldOfModuli F E)) :
    (algebraMap ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) x : F) = x :=
  IntermediateField.coe_inclusion _ x

instance instIsScalarTowerFieldOfModuliTripodal :
    IsScalarTower ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) F :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
      algebraMap_fieldOfModuli_tripodal_apply]

instance instIsScalarTowerRatFieldOfModuliTripodal :
    IsScalarTower ℚ ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

instance instFiniteDimensionalFieldOfModuliTripodal :
    FiniteDimensional ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) :=
  Module.Finite.of_restrictScalars_finite ℚ _ _

/-- `[F_tpd : ℚ] = [F_tpd : F_mod]·d_mod`. -/
lemma finrank_tripodal_eq_mul :
    Module.finrank ℚ ↥(tripodalFieldOf F E) =
      Module.finrank ℚ ↥(fieldOfModuli F E) *
        Module.finrank ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) :=
  (Module.finrank_mul_finrank ℚ ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E)).symm

variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] (L : IntermediateField F Fbar)
  [NumberField ↥L]

/-- The place of `F_tpd` below a place of a finite extension `L` of `F`. -/
noncomputable abbrev placeTpd (v : FinitePlace ↥L) : FinitePlace ↥(tripodalFieldOf F E) :=
  Tripod.placeUnder (k := ↥(tripodalFieldOf F E)) v

variable {F E L}

lemma liesOver_placeTpd (v : FinitePlace ↥L) : FinitePlace.LiesOver v (placeTpd F E L v) :=
  Tripod.liesOver_placeUnder v

lemma residueChar_placeTpd (v : FinitePlace ↥L) :
    residueChar (placeTpd F E L v) = residueChar v :=
  (Tripod.residueChar_eq_of_liesOver (liesOver_placeTpd v)).symm

/-- `e_v = e_u · e(v/u)` for `u` the place of `F_tpd` below `v`. -/
lemma ramIdx_eq_ramIdx_placeTpd_mul (v : FinitePlace ↥L) :
    ramIdx (↥L) v =
      ramIdx ↥(tripodalFieldOf F E) (placeTpd F E L v) * Tripod.relRamIdx v (placeTpd F E L v) :=
  Tripod.ramIdx_eq_mul (liesOver_placeTpd v)

/-- `f_v = f_u · f(v/u)` for `u` the place of `F_tpd` below `v`. -/
lemma inertDeg_eq_inertDeg_placeTpd_mul (v : FinitePlace ↥L) :
    inertDeg (↥L) v =
      inertDeg ↥(tripodalFieldOf F E) (placeTpd F E L v) * Tripod.relInertDeg v (placeTpd F E L v) :=
  Tripod.inertDeg_eq_mul (liesOver_placeTpd v)

end Fields

/-! ### The residual local facts -/

section Facts

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))
variable (Pr : AdmissiblePrimeData F E Fbar VBad) [NumberField ↥Pr.torsionField]

/-- **`F_tpd/F_mod` at the bad places**: `e(u/u₀) ≤ 2` for every place `u` of `F_tpd` over a
place `u₀ ∈ V_mod^bad` of `F_mod` (IUT IV, Proposition 1.8; a theorem for the curves of the
tripod, `Iut.Tripod.relRamIdx_tpd_le_two`). -/
def RelRamIdxModLeTwo : Prop :=
  ∀ (u : FinitePlace ↥(tripodalFieldOf F E)) (u₀ : FinitePlace ↥(fieldOfModuli F E)),
    u₀ ∈ VBad → FinitePlace.LiesOver u u₀ → Tripod.relRamIdx u u₀ ≤ 2

/-- **The local facts of the tower** `F_mod ⊆ F_tpd ⊆ F ⊆ K` (IUT IV, Proposition 1.8; see
the module docstring): the wild ramification bound (from which the different bound of
Proposition 1.3 follows by Serre's bound), Néron–Ogg–Shafarevich, and the ramification
bound away from `2·3·5·ℓ`. -/
structure TowerLocalFacts : Prop where
  /-- **The wild ramification bound** (the tameness of Proposition 1.8 with the degree
  divisibilities `[K : F] ∣ |GL₂(𝔽_ℓ)|`, `[F : F_tpd] ∣ 2¹²·3²·5`): `v_p(e(v/u)) ≤ c_p`.
  Together with Serre's bound on the different this gives the different bound of
  Proposition 1.3, `Iut.TowerLocalFacts.ordAt_different_le`. -/
  padicValNat_relRamIdx_le : ∀ v : FinitePlace ↥Pr.torsionField,
    padicValNat (residueChar v) (Tripod.relRamIdx v (placeTpd F E Pr.torsionField v)) ≤
      wildConst Pr.ℓ (residueChar v)
  /-- **Néron–Ogg–Shafarevich**: `K/F_tpd` is unramified at the places of residue
  characteristic `∉ {2, 3, 5, ℓ}` over a place of `F_tpd` that is not bad. -/
  relRamIdx_eq_one : ∀ v : FinitePlace ↥Pr.torsionField,
    residueChar v ∉ ({2, 3, 5, Pr.ℓ} : Finset ℕ) →
    ¬ IsBadTpdOf F E VBad (placeTpd F E Pr.torsionField v) →
    Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) = 1
  /-- **The ramification bound away from `2·3·5·ℓ`**: `e(v/u) ≤ 30ℓ`. -/
  relRamIdx_le : ∀ v : FinitePlace ↥Pr.torsionField,
    residueChar v ∉ ({2, 3, 5, Pr.ℓ} : Finset ℕ) →
    Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) ≤ 30 * Pr.ℓ

end Facts

end AbcAdaptation.Reference.Iut
