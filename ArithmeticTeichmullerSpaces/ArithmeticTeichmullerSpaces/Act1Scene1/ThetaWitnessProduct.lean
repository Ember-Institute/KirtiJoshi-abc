import ArithmeticTeichmullerSpaces.Act1Scene1.ThetaLogSignAudit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalQRootNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
source-id: JT-ATS-III-NORMALIZED-THETA-WITNESS-PRODUCT
source: Joshi III, proof of `th:moccor-Mochizuki-form1` (3460--3486),
`le:volume-lemma2` (3531--3543), `le:volume-lemma3` (3576--3583), and the
sign convention before `cor:cor312` (3634--3650).
fidelity: proves the finite real product estimate with normalized exponents
`j² / ellStar²`, including weights in `[0,1]`, and instantiates its base
radius with the actual canonical q-root's residue-degree corrected norm.
These real component radii still need to be realized by theta lifts in the
different untilts and by elements of the actual tensor/hull region.  No
Haar volume, containment, or target thetaVolume is assumed or constructed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ThetaWitnessProduct

open JoshiTeich.Prologue
open scoped BigOperators

universe u

/-- One-based procession labels with the paper's normalized square exponent. -/
noncomputable def scale (n : ℕ) (j : Fin n) : ℝ :=
  (((j.1 + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 2

theorem scale_mem_unitInterval (n : ℕ) (j : Fin n) :
    0 ≤ scale n j ∧ scale n j ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le j.1).trans_lt j.2
  have hj : ((j.1 + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt j.2
  have hratio0 : 0 ≤ ((j.1 + 1 : ℕ) : ℝ) / (n : ℝ) := by positivity
  have hratio1 : ((j.1 + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 :=
    (div_le_one hn).2 hj
  unfold scale
  constructor
  · exact sq_nonneg _
  · nlinarith

/-- The product of the weighted, normalized component radii. -/
noncomputable def product (a : ℝ) (n : ℕ) (γ : Fin n → ℝ) : ℝ :=
  ∏ j : Fin n, a ^ (γ j * scale n j)

theorem product_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (n : ℕ) (γ : Fin n → ℝ) (hγ : ∀ j, 0 ≤ γ j ∧ γ j ≤ 1) :
    0 < product a n γ ∧ a ^ n ≤ product a n γ ∧ product a n γ ≤ 1 := by
  have hExp (j : Fin n) : 0 ≤ γ j * scale n j ∧ γ j * scale n j ≤ 1 := by
    have hscale := scale_mem_unitInterval n j
    refine ⟨mul_nonneg (hγ j).1 hscale.1, ?_⟩
    simpa using mul_le_mul (hγ j).2 hscale.2 hscale.1 (by norm_num : (0 : ℝ) ≤ 1)
  unfold product
  refine ⟨Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos ha0 _), ?_, ?_⟩
  · have hprod : (∏ _j : Fin n, a) ≤ ∏ j : Fin n, a ^ (γ j * scale n j) := by
      exact Finset.prod_le_prod (fun _ _ => ha0.le)
        (fun j _ => Real.self_le_rpow_of_le_one ha0.le ha1 (hExp j).2)
    simpa using hprod
  · exact Finset.prod_le_one
      (fun j _ => (Real.rpow_pos_of_pos ha0 _).le)
      (fun j _ => Real.rpow_le_one ha0.le ha1 (hExp j).1)

theorem negLog_product_eq {a : ℝ} (ha0 : 0 < a)
    (n : ℕ) (γ : Fin n → ℝ) :
    -Real.log (product a n γ) =
      ∑ j : Fin n, (γ j * scale n j) * (-Real.log a) := by
  unfold product
  rw [Real.log_prod (fun j _ => (Real.rpow_pos_of_pos ha0 _).ne')]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.log_rpow ha0]
  ring

/-- The positive logarithmic cost has the correct sign and direction. -/
theorem negLog_product_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (n : ℕ) (γ : Fin n → ℝ) (hγ : ∀ j, 0 ≤ γ j ∧ γ j ≤ 1) :
    0 ≤ -Real.log (product a n γ) ∧
      -Real.log (product a n γ) ≤ (n : ℝ) * (-Real.log a) := by
  have hb := product_bounds ha0 ha1 n γ hγ
  refine ⟨neg_nonneg.mpr (Real.log_nonpos hb.1.le hb.2.2), ?_⟩
  have hlog := Real.log_le_log (pow_pos ha0 n) hb.2.1
  rw [Real.log_pow] at hlog
  nlinarith

section ActualRoot

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-- The procession length is fixed by the actual admissible prime. -/
def ellStar : ℕ := (D.prime.ℓ - 1) / 2

theorem ellStar_pos : 0 < ellStar D := by
  have h := D.prime.five_le
  unfold ellStar
  omega

theorem paperRootNorm_pos_lt_one
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    0 < CanonicalQRootNorm.paperRootNorm D v ∧
      CanonicalQRootNorm.paperRootNorm D v < 1 := by
  have h0 : 0 < ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ :=
    norm_pos_iff.mpr ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot_ne_zero v)
  have h1 := IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D v
  have hf : (0 : ℝ) < Arithmetic.inertDeg v.1 := by
    exact_mod_cast Arithmetic.inertDeg_pos v.1
  unfold CanonicalQRootNorm.paperRootNorm
  refine ⟨Real.rpow_pos_of_pos h0 _, ?_⟩
  exact Real.rpow_lt_one h0.le h1 (one_div_pos.mpr hf)

/-- An actual source radius supplies the finite weighted witness estimate,
without a detached norm law or a target volume input. -/
theorem canonical_qroot_witness_bounds
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset)
    (γ : Fin (ellStar D) → ℝ) (hγ : ∀ j, 0 ≤ γ j ∧ γ j ≤ 1) :
    let a := CanonicalQRootNorm.paperRootNorm D v
    a ^ ellStar D ≤ product a (ellStar D) γ ∧
      0 ≤ -Real.log (product a (ellStar D) γ) ∧
      -Real.log (product a (ellStar D) γ) ≤
        (ellStar D : ℝ) * (-Real.log a) := by
  have ha := paperRootNorm_pos_lt_one D v
  have hprod := product_bounds ha.1 ha.2.le (ellStar D) γ hγ
  have hlog := negLog_product_bounds ha.1 ha.2.le (ellStar D) γ hγ
  exact ⟨hprod.2.1, hlog⟩

end ActualRoot

end JoshiTeich.Act1Scene1.ThetaWitnessProduct
