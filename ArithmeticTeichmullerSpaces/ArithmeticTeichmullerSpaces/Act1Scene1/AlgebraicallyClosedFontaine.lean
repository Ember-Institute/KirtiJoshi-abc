import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAdicFontaine
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
source-id: JT-SCENE1-ALGEBRAICALLY-CLOSED-FONTAINE
source: Joshi, Arithmetic Holomorphic Structures, lem:perfectoid (574--581);
Mathlib IsAlgClosed.exists_pow_nat_eq and surjective_fontaineTheta.
fidelity: on an explicitly supplied complete algebraically closed ultrametric
field, its actual norm valuation ring is p-adically complete when 0 < norm p < 1.
Integral roots prove Frobenius modulo p and Fontaine theta surjective. Roots
also rule out a largest norm below one. No holomorphoid or field existence is
postulated, and no new Prologue contract is introduced. Original proofs.
boundary: Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.LocalGeometricFontaine

open JoshiTeich.Prologue
open scoped Topology
universe u
noncomputable section
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω]

abbrev integerRing := (NormedField.valuation (K := Ω)).integer

theorem mem_integerRing (x : Ω) : x ∈ integerRing Ω ↔ ‖x‖ ≤ 1 := by
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  exact NNReal.coe_le_coe.symm

theorem integerRing_eq_closedBall : (integerRing Ω : Set Ω) = Metric.closedBall 0 1 := by
  ext x
  change x ∈ integerRing Ω ↔ x ∈ Metric.closedBall 0 1
  rw [mem_integerRing, Metric.mem_closedBall, dist_zero_right]

theorem principalIdeal_eq_closedBall (z : integerRing Ω) :
    (Ideal.span {z} : Set (integerRing Ω)) =
      ((↑) : integerRing Ω → Ω) ⁻¹' Metric.closedBall 0 ‖(z : Ω)‖ := by
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  ext x
  change ‖(x : Ω)‖₊ ≤ ‖(z : Ω)‖₊ ↔ dist (x : Ω) 0 ≤ ‖(z : Ω)‖
  rw [dist_zero_right]
  exact NNReal.coe_le_coe.symm

theorem principalIdeal_isOpen (z : integerRing Ω) (hz : z ≠ 0) :
    IsOpen (Ideal.span {z} : Set (integerRing Ω)) := by
  rw [principalIdeal_eq_closedBall]
  exact (IsUltrametricDist.isOpen_closedBall _
    (norm_ne_zero_iff.mpr (Subtype.coe_ne_coe.mpr hz))).preimage continuous_subtype_val

instance integerRing_completeSpace [CompleteSpace Ω] : CompleteSpace (integerRing Ω) := by
  apply IsComplete.completeSpace_coe
  rw [integerRing_eq_closedBall]
  exact Metric.isClosed_closedBall.isComplete

variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

omit [Fact p.Prime] in
theorem prime_nonunit : ¬ IsUnit (p : integerRing Ω) := by
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change ‖(p : Ω)‖₊ < 1
  exact_mod_cast hp.out.2

instance primeNonunitFact : Fact (¬ IsUnit (p : integerRing Ω)) := ⟨prime_nonunit Ω p⟩

omit [Fact p.Prime] in
theorem integerRing_isAdic : IsAdic (Ideal.span {(p : integerRing Ω)}) := by
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [Ideal.span_singleton_pow]
    apply principalIdeal_isOpen
    apply pow_ne_zero n
    intro h
    exact (norm_pos_iff.mp hp.out.1) (congrArg (fun x : integerRing Ω => (x : Ω)) h)
  · intro S hS
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp.out.2
    refine ⟨n, ?_⟩
    rw [Ideal.span_singleton_pow, principalIdeal_eq_closedBall]
    intro x hx
    apply hball
    rw [Metric.mem_ball]
    change dist (x : Ω) 0 < ε
    rw [dist_zero_right]
    have hx' : ‖(x : Ω)‖ ≤ ‖(p : Ω)‖ ^ n := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        Subring.coe_pow, Subring.coe_natCast, norm_pow] using hx
    exact hx'.trans_lt hn

instance integerRing_isAdicComplete [CompleteSpace Ω] :
    IsAdicComplete (Ideal.span {(p : integerRing Ω)}) (integerRing Ω) :=
  (integerRing_isAdic Ω p).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

variable [IsAlgClosed Ω]

/-- An integral element has an integral root, using the actual field norm. -/
theorem integral_pow_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun x : integerRing Ω => x ^ n) := by
  intro a
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : Ω) hn
  have hzn : ‖z‖ ^ n = ‖(a : Ω)‖ := by rw [← norm_pow, hz]
  have hzle : ‖z‖ ≤ 1 :=
    (pow_le_one_iff_of_nonneg (norm_nonneg z) hn.ne').mp
      (hzn ▸ (mem_integerRing Ω (a : Ω)).mp a.property)
  exact ⟨⟨z, (mem_integerRing Ω z).mpr hzle⟩, Subtype.ext hz⟩

omit [IsUltrametricDist Ω] in
/-- The norm value group has no greatest value strictly below one. -/
theorem exists_norm_between (x : Ω) (hx0 : 0 < ‖x‖) (hx1 : ‖x‖ < 1) :
    ∃ y : Ω, ‖x‖ < ‖y‖ ∧ ‖y‖ < 1 := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x zero_lt_two
  have hnorm : ‖y‖ ^ 2 = ‖x‖ := by rw [← norm_pow, hy]
  have hy0 : 0 < ‖y‖ := by
    apply norm_pos_iff.mpr
    intro h
    rw [h, zero_pow (by decide)] at hy
    exact (norm_pos_iff.mp hx0) hy.symm
  have hy1 : ‖y‖ < 1 :=
    (pow_lt_one_iff_of_nonneg (norm_nonneg y) (by decide : 2 ≠ 0)).mp (hnorm ▸ hx1)
  exact ⟨y, hnorm ▸ pow_lt_self_of_lt_one₀ hy0 hy1 (by decide : 1 < 2), hy1⟩

theorem frobenius_modP_surjective :
    Function.Surjective (frobenius (ModP (integerRing Ω) p) p) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, hb⟩ := integral_pow_surjective Ω p (Fact.out : p.Prime).pos a
  change b ^ p = a at hb
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [frobenius_def, ← map_pow, hb]

theorem theta_surjective [CompleteSpace Ω] :
    Function.Surjective (Perfectoid.thetaMap (O := integerRing Ω) (p := p)) :=
  surjective_fontaineTheta (frobenius_modP_surjective Ω p)

end
end JoshiTeich.Act1Scene1.LocalGeometricFontaine
