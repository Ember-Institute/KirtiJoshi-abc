import ArithmeticTeichmullerSpaces.Act1Scene1.Boundary

namespace JoshiTeich.Act1Scene1

open scoped BigOperators

universe u v

/-!
source-id: IUT-COR312-FINITE-WEIGHTED-AVERAGING
source: `refer/iut/Iut/Concrete/LocalEstimate.lean`,
`sum_bound_eval` in the `LocalEstimate` namespace.
fidelity: ports the finite weighted-average calculation and adds the
pointwise-bound consumer used by packet/hull volume estimates.
boundary: Scene1/Derived

The theorem is independent of theta data and does not construct a local
IUT theory, a packet/hull region, or a theta-volume bound.  Those source
objects remain explicit obligations for the eventual Scene1 adapter.
-/

namespace IutFiniteWeightedAveraging

/-! The following three identities are the finite product-weight calculations
from `refer/iut/Iut/Concrete/Invariants.lean`.  They are kept local to this
Scene1 adapter so that the source theorem can be consumed without importing
the reference project namespace. -/

section Average

variable {ι : Type u} {E : Type v} [Fintype ι] [Fintype E] [DecidableEq ι]

private lemma sum_prod_tuple (w : E → ℝ) :
    ∑ c : ι → E, ∏ i, w (c i) = (∑ e, w e) ^ Fintype.card ι := by
  rw [← Fintype.prod_sum (fun _ : ι => w)]
  simp

private lemma sum_prod_tuple_mul_coord (w : E → ℝ) (hw : ∑ e, w e = 1)
    (f : E → ℝ) (i₀ : ι) :
    ∑ c : ι → E, (∏ i, w (c i)) * f (c i₀) = ∑ e, w e * f e := by
  let g : ι → E → ℝ := fun i e => if i = i₀ then w e * f e else w e
  have hg : ∀ c : ι → E, (∏ i, w (c i)) * f (c i₀) = ∏ i, g i (c i) := by
    intro c
    rw [← Finset.mul_prod_erase Finset.univ (fun i => g i (c i)) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ (fun i => w (c i)) (Finset.mem_univ i₀)]
    have hprod : ∏ i ∈ Finset.univ.erase i₀, g i (c i) =
        ∏ i ∈ Finset.univ.erase i₀, w (c i) :=
      Finset.prod_congr rfl fun i hi => by
        simp [g, (Finset.mem_erase.mp hi).1]
    rw [hprod]
    simp only [g, ite_true]
    ring
  simp_rw [hg]
  rw [← Fintype.prod_sum g,
    ← Finset.mul_prod_erase Finset.univ (fun i => ∑ e, g i e) (Finset.mem_univ i₀)]
  have hprod : ∏ i ∈ Finset.univ.erase i₀, ∑ e, g i e = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp [g, (Finset.mem_erase.mp hi).1, hw]
  rw [hprod, mul_one]
  simp [g]

private lemma sum_prod_tuple_mul_sum (w : E → ℝ) (hw : ∑ e, w e = 1)
    (f : E → ℝ) :
    ∑ c : ι → E, (∏ i, w (c i)) * ∑ i, f (c i) =
      Fintype.card ι * ∑ e, w e * f e := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_prod_tuple_mul_coord w hw f]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

private lemma sum_prod_tuple_eq_one (w : E → ℝ) (hw : ∑ e, w e = 1)
    [inst : Fintype (ι → E)] :
    ∑ c : ι → E, ∏ i, w (c i) = 1 := by
  classical
  rw [Subsingleton.elim inst Pi.instFintype]
  clear inst
  rw [sum_prod_tuple, hw, one_pow]

end Average

variable {ι : Type u} {E : Type v} [Fintype ι] [Fintype E]

/-- The finite product-weight averaging identity used in IUT's local estimate.
The proof is a direct finite-sum transport of the normalized product weights.
-/
theorem sum_bound_eval
    (w : E → ℝ)
    (hw : ∑ e, w e = 1)
    (o d : E → ℝ) (J L T : ℝ) (j : ι) [inst : Fintype (ι → E)] :
    ∑ c : ι → E,
        (∏ l, w (c l)) *
          ((-J * o (c j) + ∑ l, d (c l) + 1) * L + ∑ _l : ι, T) =
      (-J * ∑ e, w e * o e + Fintype.card ι * ∑ e, w e * d e + 1) * L +
        Fintype.card ι * T := by
  classical
  rw [Subsingleton.elim inst Pi.instFintype]
  clear inst
  have key : ∀ c : ι → E,
      (∏ l, w (c l)) *
          ((-J * o (c j) + ∑ l, d (c l) + 1) * L + ∑ _l : ι, T) =
        (-J * L) * ((∏ l, w (c l)) * o (c j)) +
          L * ((∏ l, w (c l)) * ∑ l, d (c l)) +
          L * (∏ l, w (c l)) +
          (Fintype.card ι * T) * (∏ l, w (c l)) := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_prod_tuple_mul_coord w hw o j, sum_prod_tuple_mul_sum w hw d,
    sum_prod_tuple_eq_one w hw]
  ring

/-- A pointwise local estimate transports to the corresponding finite weighted
packet estimate.  This is the direct consumer of `sum_bound_eval` used by a
future concrete theta-region adapter.
-/
theorem weighted_sum_le_of_pointwise
    (w : E → ℝ)
    (hw : ∑ e, w e = 1)
    (hw_nonneg : ∀ e, 0 ≤ w e)
    (o d : E → ℝ) (J L T : ℝ) (j : ι)
    (localValue : (ι → E) → ℝ) [inst : Fintype (ι → E)]
    (hLocal : ∀ c,
      localValue c ≤
        (-J * o (c j) + ∑ l, d (c l) + 1) * L + ∑ _l : ι, T) :
    ∑ c : ι → E, (∏ l, w (c l)) * localValue c ≤
      (-J * ∑ e, w e * o e + Fintype.card ι * ∑ e, w e * d e + 1) * L +
        Fintype.card ι * T := by
  classical
  calc
    ∑ c : ι → E, (∏ l, w (c l)) * localValue c ≤
        ∑ c : ι → E,
          (∏ l, w (c l)) *
            ((-J * o (c j) + ∑ l, d (c l) + 1) * L + ∑ _l : ι, T) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hLocal c) (Finset.prod_nonneg fun l hl => hw_nonneg (c l))
    _ = (-J * ∑ e, w e * o e + Fintype.card ι * ∑ e, w e * d e + 1) * L +
        Fintype.card ι * T := sum_bound_eval w hw o d J L T j

end IutFiniteWeightedAveraging

end JoshiTeich.Act1Scene1
