/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/-
Original repository https://github.com/lana-agents/iut
Original path Iut/Tripod/TorsionDegree.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound
import Solutions.Source_TripodTorsionRepresentation
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve
open scoped Classical IntermediateField

section Bound

/-- `|GL₂(𝔽_n)| = (n² − 1)(n² − n)` for `n` prime. -/
theorem card_GL_two (n : ℕ) [Fact n.Prime] :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod n)) = (n ^ 2 - 1) * (n ^ 2 - n) := by
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
  simp

variable (K : IntermediateField ℚ Qbar) {l : Qbar} (hl : l ∈ K) (n : ℕ) [Fact n.Prime]
variable (b : AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n))

/-- The index of `ker ρ` is at most `|GL₂(𝔽_n)|`. -/
theorem torsionRep_ker_index_le :
    (torsionRep K hl n b).ker.index ≤ (n ^ 2 - 1) * (n ^ 2 - n) := by
  rw [Subgroup.index_ker, ← card_GL_two n]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

include hl b in
/-- **The relative torsion degree bound**: `[K(E_λ[n]) : K] ≤ (n² − 1)(n² − n)`. -/
theorem finrank_adjoin_torsionCoords_le :
    Module.finrank K (IntermediateField.adjoin K (torsionCoords l n)) ≤
      (n ^ 2 - 1) * (n ^ 2 - n) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← torsionRep_ker K hl n b]
  exact torsionRep_ker_index_le K hl n b

end Bound

/-- **The torsion degree bound** (`Iut.Tripod.TorsionDegreeBound`) for prime `n`, given a basis
`E_λ(ℚ̄)[n] ≅ (ℤ/n)²`. -/
theorem torsionDegreeBound (l : Qbar) (n : ℕ) [Fact n.Prime]
    (hbasis : Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n))) :
    TorsionDegreeBound l n := by
  intro K hK hl
  obtain ⟨b⟩ := hbasis
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  calc Module.finrank ℚ ↥(IntermediateField.restrictScalars ℚ
        (IntermediateField.adjoin K (torsionCoords l n)))
      = Module.finrank ℚ K * Module.finrank K (IntermediateField.adjoin K (torsionCoords l n)) :=
        (Module.finrank_mul_finrank ℚ K (IntermediateField.adjoin K (torsionCoords l n))).symm
    _ ≤ Module.finrank ℚ K * ((n ^ 2 - 1) * (n ^ 2 - n)) :=
        Nat.mul_le_mul_left _ (finrank_adjoin_torsionCoords_le K hl n b)
    _ = (n ^ 2 - 1) * (n ^ 2 - n) * Module.finrank ℚ K := mul_comm _ _

/-- The torsion degree bound for `n = 3`. -/
theorem torsionDegreeBound_three (l : Qbar)
    (hbasis : Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point 3 ≃+ (Fin 2 → ZMod 3))) :
    TorsionDegreeBound l 3 :=
  torsionDegreeBound l 3 hbasis

/-- The torsion degree bound for `n = 5`. -/
theorem torsionDegreeBound_five (l : Qbar)
    (hbasis : Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point 5 ≃+ (Fin 2 → ZMod 5))) :
    TorsionDegreeBound l 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  torsionDegreeBound l 5 hbasis

/-- The degree-bound input at `n = 3` from pointwise `3`-torsion bases. -/
theorem torsionDegreeBound_three_onPt
    (hbasis : ∀ x : Pt,
      Nonempty (AddSubgroup.torsionBy (legendre x.1).toAffine.Point 3 ≃+ (Fin 2 → ZMod 3))) :
    ∀ x : Pt, TorsionDegreeBound x.1 3 :=
  fun x => torsionDegreeBound_three x.1 (hbasis x)

/-- The degree-bound input at `n = 5` from pointwise `5`-torsion bases. -/
theorem torsionDegreeBound_five_onPt
    (hbasis : ∀ x : Pt,
      Nonempty (AddSubgroup.torsionBy (legendre x.1).toAffine.Point 5 ≃+ (Fin 2 → ZMod 5))) :
    ∀ x : Pt, TorsionDegreeBound x.1 5 :=
  fun x => torsionDegreeBound_five x.1 (hbasis x)

end AbcAdaptation.Tripod
