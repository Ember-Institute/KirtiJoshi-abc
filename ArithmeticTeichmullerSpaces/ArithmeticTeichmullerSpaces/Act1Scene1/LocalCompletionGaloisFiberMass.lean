import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionGaloisDegree

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-GALOIS-FIBER-MASS
source: the complete finite-place local-degree sum and Galois conjugacy of
places; Joshi III `eq:weights` and its representative multiplicity accounting.
fidelity: computes the actual full-fibre multiplicity and the pushforward of
inertDeg/[L:Q]. Its mass is the base weight divided by relative ramification;
mass one is not an input. Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no identification with paper representatives.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField JoshiTeich.Prologue.Arithmetic
open scoped BigOperators
universe u
noncomputable section
variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [IsGalois K L]

theorem card_mul_relativeDegree_eq_finrank
    (w : FinitePlace K) (S : Finset (FinitePlace L))
    (hS : ∀ z, z ∈ S ↔ Ideal.LiesOver z.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (v : FinitePlace L) (hv : v ∈ S) :
    S.card * (relRamIdx v w * relInertDeg v w) = Module.finrank K L := by
  have hvw := (hS v).mp hv
  have hconstant : (∑ z ∈ S, localDeg z) = S.card * localDeg v := by
    calc
      _ = ∑ _z ∈ S, localDeg v :=
        Finset.sum_congr rfl fun z hz => localDeg_eq_of_galois_liesOver ((hS z).mp hz) hvw
      _ = S.card * localDeg v := by simp
  apply Nat.eq_of_mul_eq_mul_left (localDeg_pos w)
  calc
    localDeg w * (S.card * (relRamIdx v w * relInertDeg v w)) = S.card * localDeg v := by
      rw [localDeg_eq_mul hvw]
      ring
    _ = Module.finrank K L * localDeg w :=
      hconstant.symm.trans (sum_localDeg_liesOver w S hS)
    _ = localDeg w * Module.finrank K L := Nat.mul_comm _ _

theorem qPilotWeight_sum_eq_base_div_relativeRamIdx
    (w : FinitePlace K) (S : Finset (FinitePlace L))
    (hS : ∀ z, z ∈ S ↔ Ideal.LiesOver z.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (v : FinitePlace L) (hv : v ∈ S) :
    (∑ z ∈ S, qPilotWeight z) = qPilotWeight w / (relRamIdx v w : ℝ) := by
  have hvw := (hS v).mp hv
  have hpoint (z : FinitePlace L) (hz : z ∈ S) :
      localDeg z = (ramIdx w * relRamIdx v w) * inertDeg z := by
    unfold localDeg
    rw [ramIdx_eq_of_galois_liesOver ((hS z).mp hz) hvw, ramIdx_eq_mul hvw]
  have hsum : (ramIdx w * relRamIdx v w) * (∑ z ∈ S, inertDeg z) =
      Module.finrank K L * (ramIdx w * inertDeg w) := by
    calc
      _ = ∑ z ∈ S, localDeg z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z hz => (hpoint z hz).symm
      _ = Module.finrank K L * localDeg w := sum_localDeg_liesOver w S hS
      _ = _ := rfl
  have hnat : relRamIdx v w * (∑ z ∈ S, inertDeg z) =
      Module.finrank K L * inertDeg w := by
    apply Nat.eq_of_mul_eq_mul_left (ramIdx_pos w)
    calc
      _ = (ramIdx w * relRamIdx v w) * (∑ z ∈ S, inertDeg z) := by ring
      _ = Module.finrank K L * (ramIdx w * inertDeg w) := hsum
      _ = _ := by ring
  have hmass : (relRamIdx v w : ℝ) * (∑ z ∈ S, (inertDeg z : ℝ)) =
      (Module.finrank K L : ℝ) * inertDeg w := by exact_mod_cast hnat
  have hglobal : (Module.finrank ℚ L : ℝ) =
      (Module.finrank ℚ K : ℝ) * Module.finrank K L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K L).symm
  have he : (relRamIdx v w : ℝ) ≠ 0 := by exact_mod_cast relRamIdx_ne_zero hvw
  unfold qPilotWeight
  rw [← Finset.sum_div]
  apply (eq_div_iff he).mpr
  rw [div_mul_eq_mul_div]
  apply (div_eq_div_iff (finrank_pos (K := L)).ne' (finrank_pos (K := K)).ne').mpr
  rw [hglobal]
  linear_combination (Module.finrank ℚ K : ℝ) * hmass

end
end JoshiTeich.Act1Scene1.LocalCompletion
