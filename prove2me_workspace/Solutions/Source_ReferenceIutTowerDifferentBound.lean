/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/DifferentBound.lean
-/
import Solutions.Source_ReferenceIutTowerDifferentPowers
import Solutions.Source_ReferenceIutTowerLocalFacts
import Solutions.Source_ReferenceIutTowerSerreBound

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Serre

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **Serre's bound on the different of an extension of number fields** (IUT IV,
Proposition 1.3): for a place `v` of `K` over `u` of `k`,
`ord_v(𝔇_{K/k}) + 1 ≤ e(v/u) + e_v·v_p(e(v/u))`. -/
theorem ordAt_differentIdeal_add_one_le {v : FinitePlace K} {u : FinitePlace k}
    (hvu : FinitePlace.LiesOver v u) :
    ordAt (differentIdeal (𝓞 k) (𝓞 K)) v + 1 ≤
      Tripod.relRamIdx v u + ramIdx K v * padicValNat (residueChar v) (Tripod.relRamIdx v u) := by
  haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hvu
  haveI : u.maximalIdeal.asIdeal.IsMaximal :=
    u.maximalIdeal.isPrime.isMaximal u.maximalIdeal.ne_bot
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : Finite (𝓞 k ⧸ u.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ u.maximalIdeal.ne_bot
  have he : Tripod.relRamIdx v u ≠ 0 := Tripod.relRamIdx_ne_zero hvu
  set κ := Tripod.ramIdx k u * padicValNat (residueChar u) (Tripod.relRamIdx v u) with hκdef
  have hκ : ((Tripod.relRamIdx v u : ℕ) : 𝓞 k) ∉ u.maximalIdeal.asIdeal ^ (κ + 1) :=
    natCast_notMem_pow_ramIdx_mul_padicValNat u he
  have h := Serre.not_pow_dvd_differentIdeal u.maximalIdeal.asIdeal v.maximalIdeal.asIdeal
    u.maximalIdeal.ne_bot κ hκ
  have hpos : 1 ≤ Tripod.relRamIdx v u * (κ + 1) :=
    Nat.mul_pos (Nat.pos_of_ne_zero he) (Nat.succ_pos κ)
  have h2 := ordAt_le_of_not_pow_dvd _ differentIdeal_ne_bot v (Tripod.relRamIdx v u * (κ + 1) - 1)
    (by rwa [Nat.sub_add_cancel hpos])
  change ordAt (differentIdeal (𝓞 k) (𝓞 K)) v + 1 ≤
    Tripod.relRamIdx v u + Tripod.ramIdx K v * padicValNat (residueChar v) (Tripod.relRamIdx v u)
  have hp : residueChar v = residueChar u := Tripod.residueChar_eq_of_liesOver hvu
  rw [Tripod.ramIdx_eq_mul hvu, hp]
  have h3 : Tripod.relRamIdx v u * (κ + 1) =
      Tripod.relRamIdx v u + Tripod.ramIdx k u * Tripod.relRamIdx v u * padicValNat (residueChar u) (Tripod.relRamIdx v u) := by
    rw [hκdef]
    ring
  omega

end Serre

/-! ### The different bound of the tower -/

section Tower

universe u

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-- **The different bound** (IUT IV, Proposition 1.3 with the tameness of Proposition 1.8):
`ord_v(𝔇_{K/F_tpd}) + 1 ≤ e(v/u) + e_v·c_p`, from Serre's bound and the wild ramification
bound `v_p(e(v/u)) ≤ c_p` of the local facts. -/
theorem TowerLocalFacts.ordAt_different_le (H : TowerLocalFacts E VBad Pr)
    (v : FinitePlace ↥Pr.torsionField) :
    ordAt (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) v + 1 ≤
      Tripod.relRamIdx v (placeTpd F E Pr.torsionField v) +
        ramIdx (↥Pr.torsionField) v * wildConst Pr.ℓ (residueChar v) :=
  (ordAt_differentIdeal_add_one_le (liesOver_placeTpd v)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (H.padicValNat_relRamIdx_le v)) _)

end Tower

end AbcAdaptation.Reference.Iut
