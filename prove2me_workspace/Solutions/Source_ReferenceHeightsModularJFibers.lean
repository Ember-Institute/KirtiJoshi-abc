/-
Original repository https://github.com/lana-agents/heights
Original revision 721496ca4c158e511d25d8ccf6bfe8503eda73c1
Original path Heights/ModularJFibers.lean
-/
import Solutions.Source_ReferenceHeightsLatticeModular
import Solutions.Source_ReferenceHeightsPeriodPairScaling
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Fibers of the modular j-function

Equality of modular `j`-values gives an isomorphism between the corresponding
short lattice curves.  The transformation laws for `c₄` and `c₆`, together
with rigidity of the Weierstrass invariants, identify their period lattices up
to homothety.  Comparing integral bases then produces an element of
`SL(2, ℤ)` carrying one upper-half-plane parameter to the other.
-/

open scoped UpperHalfPlane MatrixGroups Manifold Modular
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup

noncomputable section
namespace AbcAdaptation.Reference.Heights

private theorem latticeCurve_c₄ (τ : ℍ) :
    (latticeCurve τ).c₄ = 12 * (periodPair τ).g₂ := by
  simp [latticeCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

private theorem latticeCurve_c₆ (τ : ℍ) :
    (latticeCurve τ).c₆ =
      216 * (periodPair τ).g₃ := by
  simp [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, latticeCurve]
  ring

private theorem exists_scale_lattice_eq_of_modularJ_eq (τ τ' : ℍ)
    (hj : modularJ τ = modularJ τ') :
    ∃ (a : ℂ) (ha : a ≠ 0),
      (periodPairScale a ha (periodPair τ)).lattice = (periodPair τ').lattice := by
  letI : (latticeCurve τ).IsElliptic := latticeCurve_isElliptic τ
  letI : (latticeCurve τ').IsElliptic := latticeCurve_isElliptic τ'
  have hcurves : (latticeCurve τ).j =
      (latticeCurve τ').j := by
    rw [latticeCurve_j_eq_modularJ, latticeCurve_j_eq_modularJ, hj]
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (latticeCurve τ) (latticeCurve τ') hcurves
  let a : ℂ := C.u
  have ha : a ≠ 0 := Units.ne_zero C.u
  refine ⟨a, ha, ?_⟩
  apply periodPair_lattice_eq_of_g₂_eq_g₃_eq
  · have hc := congrArg WeierstrassCurve.c₄ hC
    rw [WeierstrassCurve.variableChange_c₄, latticeCurve_c₄,
      latticeCurve_c₄] at hc
    rw [Units.val_inv_eq_inv_val] at hc
    rw [periodPairScale_g₂]
    dsimp [a]
    linear_combination hc / 12
  · have hc := congrArg WeierstrassCurve.c₆ hC
    rw [WeierstrassCurve.variableChange_c₆, latticeCurve_c₆,
      latticeCurve_c₆] at hc
    rw [Units.val_inv_eq_inv_val] at hc
    rw [periodPairScale_g₃]
    dsimp [a]
    linear_combination hc / 216

private theorem int_linear_combination_injective (τ : ℍ)
    {m n m' n' : ℤ}
    (h : (m : ℂ) * τ + n = (m' : ℂ) * τ + n') :
    m = m' ∧ n = n' := by
  have him : (m : ℝ) * τ.im = (m' : ℝ) * τ.im := by
    simpa using congrArg Complex.im h
  have hm : m = m' := by
    exact_mod_cast mul_right_cancel₀ τ.im_ne_zero him
  subst m'
  have hn : (n : ℂ) = (n' : ℂ) := add_left_cancel h
  exact ⟨rfl, by exact_mod_cast hn⟩

/-- Equal modular `j`-values lie in the same integral modular-group orbit. -/
theorem exists_smul_eq_of_modularJ_eq (τ τ' : ℍ)
    (hj : modularJ τ = modularJ τ') :
    ∃ γ : SL(2, ℤ), γ • τ' = τ := by
  obtain ⟨a, ha, hlat⟩ := exists_scale_lattice_eq_of_modularJ_eq τ τ' hj
  let L := periodPair τ
  let L' := periodPair τ'
  let S := periodPairScale a ha L
  have haτmem : a * (τ : ℂ) ∈ L'.lattice := by
    rw [← hlat]
    exact S.ω₁_mem_lattice
  have hamem : a ∈ L'.lattice := by
    rw [← hlat]
    have h : a * (1 : ℂ) ∈ S.lattice := S.ω₂_mem_lattice
    simpa only [mul_one] using h
  obtain ⟨A, B, hA⟩ := PeriodPair.mem_lattice.mp haτmem
  obtain ⟨C, D, hC⟩ := PeriodPair.mem_lattice.mp hamem
  have hA' : (A : ℂ) * τ' + B = a * τ := by
    simpa only [L', periodPair, mul_one] using hA
  have hC' : (C : ℂ) * τ' + D = a := by
    simpa only [L', periodPair, mul_one] using hC
  have hτ'mem : (τ' : ℂ) ∈ S.lattice := by
    rw [hlat]
    exact L'.ω₁_mem_lattice
  have h1mem : (1 : ℂ) ∈ S.lattice := by
    rw [hlat]
    exact L'.ω₂_mem_lattice
  obtain ⟨P, Q, hP⟩ := PeriodPair.mem_lattice.mp hτ'mem
  obtain ⟨R, T, hR⟩ := PeriodPair.mem_lattice.mp h1mem
  have hP' : (P : ℂ) * (a * τ) + Q * a = τ' := by
    simpa only [S, L, periodPairScale_ω₁, periodPairScale_ω₂, periodPair, mul_one] using hP
  have hR' : (R : ℂ) * (a * τ) + T * a = 1 := by
    simpa only [S, L, periodPairScale_ω₁, periodPairScale_ω₂, periodPair, mul_one] using hR
  have hPA : P * A + Q * C = 1 ∧ P * B + Q * D = 0 := by
    apply int_linear_combination_injective τ'
    calc
      ((P * A + Q * C : ℤ) : ℂ) * τ' + (P * B + Q * D : ℤ) =
          (P : ℂ) * ((A : ℂ) * τ' + B) +
            (Q : ℂ) * ((C : ℂ) * τ' + D) := by push_cast; ring
      _ = (P : ℂ) * (a * τ) + Q * a := by rw [hA', hC']
      _ = (1 : ℤ) * (τ' : ℂ) + (0 : ℤ) := by simpa using hP'
  have hRA : R * A + T * C = 0 ∧ R * B + T * D = 1 := by
    apply int_linear_combination_injective τ'
    calc
      ((R * A + T * C : ℤ) : ℂ) * τ' + (R * B + T * D : ℤ) =
          (R : ℂ) * ((A : ℂ) * τ' + B) +
            (T : ℂ) * ((C : ℂ) * τ' + D) := by push_cast; ring
      _ = (R : ℂ) * (a * τ) + T * a := by rw [hA', hC']
      _ = (0 : ℤ) * (τ' : ℂ) + (1 : ℤ) := by simpa using hR'
  have hdetprod : (P * T - Q * R) * (A * D - B * C) = 1 := by
    calc
      _ = (P * A + Q * C) * (R * B + T * D) -
          (P * B + Q * D) * (R * A + T * C) := by ring
      _ = 1 := by simp [hPA.1, hPA.2, hRA.1, hRA.2]
  have hdet_cases : A * D - B * C = 1 ∨ A * D - B * C = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetprod with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  have hτeq : (τ : ℂ) =
      ((A : ℂ) * τ' + B) / ((C : ℂ) * τ' + D) := by
    rw [hC']
    field_simp [ha]
    simpa [mul_comm] using hA'.symm
  have hformula :
      (((A : ℂ) * τ' + B) / ((C : ℂ) * τ' + D)).im =
        ((A * D - B * C : ℤ) : ℝ) * τ'.im /
          Complex.normSq ((C : ℂ) * τ' + D) := by
    rw [Complex.div_im]
    norm_num
    ring
  have hdet : A * D - B * C = 1 := by
    rcases hdet_cases with h | h
    · exact h
    · exfalso
      rw [h] at hformula
      norm_num at hformula
      rw [← hτeq] at hformula
      have hnorm : 0 < Complex.normSq ((C : ℂ) * τ' + D) := by
        rw [hC']
        exact Complex.normSq_pos.mpr ha
      have hneg : -τ'.im / Complex.normSq ((C : ℂ) * τ' + D) < 0 :=
        div_neg_of_neg_of_pos (neg_neg_of_pos τ'.im_pos) hnorm
      have htneg : τ.im < 0 := by
        rw [← UpperHalfPlane.coe_im, hformula]
        exact hneg
      exact (not_lt_of_ge τ.im_pos.le) htneg
  let γ : SL(2, ℤ) := ⟨!![A, B; C, D], by
    simp [Matrix.det_fin_two, hdet]⟩
  refine ⟨γ, ?_⟩
  rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_specialLinearGroup_apply]
  change (((A : ℝ) : ℂ) * τ' + ((B : ℝ) : ℂ)) /
    (((C : ℝ) : ℂ) * τ' + ((D : ℝ) : ℂ)) = (τ : ℂ)
  simpa only [Complex.ofReal_intCast] using hτeq.symm

end AbcAdaptation.Reference.Heights
