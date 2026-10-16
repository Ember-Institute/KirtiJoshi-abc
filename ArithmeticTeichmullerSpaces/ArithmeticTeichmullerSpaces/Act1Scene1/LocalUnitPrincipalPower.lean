import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLog
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
source-id: JT-SCENE1-LOCAL-UNIT-PRINCIPAL-POWER
source: finite residue-field multiplicative group and Joshi III 2843--2853.
fidelity: every integer-ring unit has a common prime-to-p power that is
principal. The exponent is the cardinality of the residue field minus one.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u
noncomputable section

abbrev unitIntegerRing (k : Type u) [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] : Subring k :=
  (Valued.v : Valuation k (WithZero (Multiplicative ℤ))).integer

abbrev unitResidueField (k : Type u) [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] :=
  IsLocalRing.ResidueField (unitIntegerRing k)

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
local notation "O" => unitIntegerRing k
local notation "F" => unitResidueField k
variable [hF : Finite (unitResidueField k)]

def unitResidueExponent : ℕ := Nat.card F - 1

include hF in
theorem unitResidueExponent_pos : 0 < unitResidueExponent (k := k) := by
  letI := Fintype.ofFinite F
  rw [unitResidueExponent, Nat.card_eq_fintype_card]
  exact Nat.sub_pos_of_lt Fintype.one_lt_card

variable (p : ℕ) [Fact p.Prime] [hFp : CharP (unitResidueField k) p]

include hF hFp in
theorem unitResidueExponent_coprime : p.Coprime (unitResidueExponent (k := k)) := by
  letI := Fintype.ofFinite F
  obtain ⟨f, _, hf⟩ := FiniteField.card F p
  have hq : p ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hf]
    exact dvd_pow_self p f.ne_zero
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  have hsub := Nat.dvd_sub hq hd
  have he : Nat.card F - unitResidueExponent (k := k) = 1 := by
    have h : 1 < Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    unfold unitResidueExponent
    omega
  rw [he] at hsub
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hsub)

include hF in
theorem integerUnit_pow_principal (a : Oˣ) :
    ‖((a : O) : k) ^ unitResidueExponent (k := k) - 1‖ < 1 := by
  letI := Fintype.ofFinite F
  have ha : IsLocalRing.residue O (a : O) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr a.isUnit
  have hp : IsLocalRing.residue O ((a : O) ^ unitResidueExponent (k := k) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, unitResidueExponent, Nat.card_eq_fintype_card,
      FiniteField.pow_card_sub_one_eq_one _ ha, sub_self]
  have hm := (IsLocalRing.residue_eq_zero_iff _).mp hp
  rw [IsLocalRing.mem_maximalIdeal] at hm
  exact Valued.toNormedField.norm_lt_one_iff.mpr
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hm)

end
end JoshiTeich.Act1Scene1.LocalPadicLog
