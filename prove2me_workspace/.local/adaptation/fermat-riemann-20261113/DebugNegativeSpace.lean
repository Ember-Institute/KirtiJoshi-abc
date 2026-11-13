/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Source proof adaptation: Belyi/CurveField/RiemannRochSpace.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatFunctionDivisors

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

namespace Place

variable {K : Type*} [Field K] [CharZero K] (P : Place K)

@[simp] theorem riemann_coe_ratHom (q : ℚ) : (P.ratHom q : K) = q := rfl

@[simp] theorem riemann_residue_ratHom (q : ℚ) :
    P.residue (P.ratHom q) = (q : P.ResidueField) :=
  map_ratCast (P.residue.comp P.ratHom) q

end Place

namespace RiemannDimension

open IsLocalRing

variable {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
variable [hCurve : IsCurveField M.K]
include M hDVR hCurve

local notation "L" => riemannRochSpace M hDVR
local notation "ell" => riemannEll M hDVR
local notation "pdiv" => functionDivisor M hDVR
local notation "degree" => divisorDegree M

theorem mem_L {A : Divisor M} {f : M.K} : f ∈ L A ↔ f = 0 ∨ ∀ P : Place M.K, -A P ≤ P.ord f :=
  by
  simp only [mem_riemannRochSpace, ord_eq_placeOrd]

theorem mem_L_of_ne_zero {A : Divisor M} {f : M.K} (hf : f ≠ 0) :
    f ∈ L A ↔ 0 ≤ A + pdiv f := by
  rw [mem_L, or_iff_right hf]
  refine forall_congr' fun P ↦ ?_
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, functionDivisor_apply, ord_eq_placeOrd]
  omega

theorem L_mono {A B : Divisor M} (h : A ≤ B) : L A ≤ L B :=
  riemannRochSpace_mono M hDVR h

/-! ### Transport along principal divisors -/

theorem mul_mem_L {A : Divisor M} {z f : M.K} (hz : z ≠ 0) (hf : f ∈ L (A + pdiv z)) :
    f * z ∈ L A := by
  rw [mem_L] at hf ⊢
  rcases hf with rfl | hf
  · simp
  by_cases hf0 : f = 0
  · simp [hf0]
  refine Or.inr fun P ↦ ?_
  have := hf P
  simp only [Finsupp.coe_add, Pi.add_apply, functionDivisor_apply, ord_eq_placeOrd] at this
  rw [P.ord_mul hf0 hz]
  omega

theorem mul_inv_mem_L {A : Divisor M} {z g : M.K} (hz : z ≠ 0) (hg : g ∈ L A) :
    g * z⁻¹ ∈ L (A + pdiv z) := by
  rw [mem_L] at hg ⊢
  rcases hg with rfl | hg
  · simp
  by_cases hg0 : g = 0
  · simp [hg0]
  refine Or.inr fun P ↦ ?_
  have := hg P
  simp only [Finsupp.coe_add, Pi.add_apply, functionDivisor_apply, ord_eq_placeOrd]
  rw [P.ord_mul hg0 (inv_ne_zero hz), P.ord_inv]
  omega

/-- Multiplication by `z ≠ 0` identifies `L(A + pdiv z)` with `L(A)`. -/
noncomputable def mulEquiv (A : Divisor M) {z : M.K} (hz : z ≠ 0) : L (A + pdiv z) ≃ₗ[ℚ] L A where
  toFun f := ⟨f * z, mul_mem_L M hDVR hz f.2⟩
  invFun g := ⟨g * z⁻¹, mul_inv_mem_L M hDVR hz g.2⟩
  map_add' f g := Subtype.ext (add_mul _ _ _)
  map_smul' q f := Subtype.ext (smul_mul_assoc _ _ _)
  left_inv f := Subtype.ext (by simp [hz])
  right_inv g := Subtype.ext (by simp [hz])

/-- `ℓ` is invariant under linear equivalence. -/
theorem ell_add_pdiv (A : Divisor M) {z : M.K} (hz : z ≠ 0) : ell (A + pdiv z) = ell A :=
  (mulEquiv M hDVR A hz).finrank_eq

/-! ### Adding a place -/

section Step

variable {A : Divisor M} {P : Place M.K} {π : M.K}

theorem ne_zero_of_ord_eq_one (hπ : P.ord π = 1) : π ≠ 0 := by
  rintro rfl; simp at hπ

theorem zpow_mul_mem (hπ : P.ord π = 1) {f : M.K} (hf : f ∈ L (A + Finsupp.single P 1)) :
    π ^ (A P + 1) * f ∈ P.1 := by
  rw [mem_L] at hf
  rcases hf with rfl | hf
  · simp
  by_cases hf0 : f = 0
  · simp [hf0]
  apply P.mem_of_ord_nonneg
  rw [P.ord_mul (zpow_ne_zero _ (ne_zero_of_ord_eq_one M hDVR hπ)) hf0, Place.ord_zpow, hπ]
  have := hf P
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
  omega

variable (A P) in
/-- The `ℚ`-linear map `L(A + P) → κ(P)`, `f ↦ (π^{A(P)+1} f)(P)`. -/
noncomputable def residueMap (hπ : P.ord π = 1) :
    L (A + Finsupp.single P 1) →ₗ[ℚ] P.ResidueField where
  toFun f := P.residue ⟨π ^ (A P + 1) * f, zpow_mul_mem M hDVR hπ f.2⟩
  map_add' f g := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp [mul_add]
  map_smul' q f := by
    rw [RingHom.id_apply, Rat.smul_def q (P.residue _), ← P.riemann_residue_ratHom q, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, Rat.smul_def, MulMemClass.coe_mul, Place.riemann_coe_ratHom]
    ring

theorem mem_ker_residueMap (hπ : P.ord π = 1) (f : L (A + Finsupp.single P 1)) :
    f ∈ LinearMap.ker (residueMap M hDVR A P hπ) ↔ (f : M.K) ∈ L A := by
  classical
  have hπ0 := ne_zero_of_ord_eq_one M hDVR hπ
  rw [LinearMap.mem_ker]
  change P.residue _ = 0 ↔ _
  rw [P.residue_eq_zero_iff]
  by_cases hf0 : (f : M.K) = 0
  · simp only [hf0, mul_zero]
    exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ by
      rw [show (⟨0, _⟩ : P.1) = 0 from rfl]; exact Ideal.zero_mem _⟩
  have hne : π ^ (A P + 1) * (f : M.K) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hπ0) hf0
  rw [← P.ord_pos_iff_mem_maximalIdeal (a := ⟨_, zpow_mul_mem M hDVR hπ f.2⟩) hne]
  change 0 < P.ord (π ^ (A P + 1) * (f : M.K)) ↔ _
  rw [P.ord_mul (zpow_ne_zero _ hπ0) hf0, Place.ord_zpow, hπ, mem_L, or_iff_right hf0]
  have hf := f.2
  rw [mem_L, or_iff_right hf0] at hf
  constructor
  · intro h Q
    by_cases hQ : Q = P
    · subst hQ; omega
    · have := hf Q
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg (Ne.symm hQ),
        add_zero] at this
      exact this
  · intro h
    have := h P
    omega

/-- **Adding a place** (Stichtenoth, Lemma 1.4.8): if `L(A)` is finite-dimensional, so is
`L(A + P)`, and `ℓ(A + P) ≤ ℓ(A) + deg P`. -/
theorem step (A : Divisor M) (P : Place M.K) [FiniteDimensional ℚ (L A)] :
    FiniteDimensional ℚ (L (A + Finsupp.single P 1)) ∧
      ell (A + Finsupp.single P 1) ≤ ell A + P.degree := by
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  set φ := residueMap M hDVR A P hπ
  have hle : L A ≤ L (A + Finsupp.single P 1) :=
    L_mono M hDVR (le_add_of_nonneg_right (Finsupp.single_nonneg.mpr zero_le_one))
  have hker : LinearMap.ker φ = (L A).comap (L (A + Finsupp.single P 1)).subtype := by
    ext f
    exact mem_ker_residueMap M hDVR hπ f
  let e : LinearMap.ker φ ≃ₗ[ℚ] L A :=
    (LinearEquiv.ofEq _ _ hker).trans (Submodule.comapSubtypeEquivOfLe hle)
  letI : FiniteDimensional ℚ (LinearMap.ker φ) := e.symm.finiteDimensional
  have hfin : FiniteDimensional ℚ (L (A + Finsupp.single P 1)) := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker φ ?_ ?_⟩
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq]
      exact Module.Finite.iff_fg.mp (inferInstance : FiniteDimensional ℚ (LinearMap.ker φ))
  letI := hfin
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : Module.finrank ℚ (LinearMap.range φ) ≤ P.degree := Submodule.finrank_le _
  rw [e.finrank_eq] at h1
  unfold riemannEll
  omega

theorem step_nat (P : Place M.K) (m : ℕ) (A : Divisor M) [FiniteDimensional ℚ (L A)] :
    FiniteDimensional ℚ (L (A + Finsupp.single P (m : ℤ))) ∧
      (ell (A + Finsupp.single P (m : ℤ)) : ℤ) ≤ ell A + m * P.degree := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, Finsupp.single_zero, add_zero]
    exact ⟨inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    letI := h1
    obtain ⟨h3, h4⟩ := step M hDVR (A + Finsupp.single P (m : ℤ)) P
    rw [Nat.cast_succ, Finsupp.single_add, ← add_assoc]
    refine ⟨h3, ?_⟩
    have : ((m : ℤ) + 1) * P.degree = m * P.degree + P.degree := by ring
    omega

theorem aux (D : Divisor M) (hD : 0 ≤ D) (A : Divisor M) [FiniteDimensional ℚ (L A)] :
    FiniteDimensional ℚ (L (A + D)) ∧ (ell (A + D) : ℤ) ≤ ell A + (degree D) := by
  classical
  induction D using Finsupp.induction generalizing A with
  | zero =>
    rw [add_zero]
    exact ⟨inferInstance, by simp⟩
  | single_add P b f hPf _ ih =>
    have hfP : f P = 0 := Finsupp.notMem_support_iff.mp hPf
    have hb : 0 ≤ b := by
      have := hD P
      simpa [hfP] using this
    have hf : 0 ≤ f := by
      intro Q
      by_cases hQ : Q = P
      · subst hQ; simp [hfP]
      · have := hD Q
        simpa [Finsupp.single_apply, Ne.symm hQ] using this
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    obtain ⟨h1, h2⟩ := step_nat M hDVR P m A
    letI := h1
    obtain ⟨h3, h4⟩ := ih hf (A + Finsupp.single P (m : ℤ))
    rw [← add_assoc]
    refine ⟨h3, ?_⟩
    rw [divisorDegree_add, divisorDegree_single]
    omega

end Step

/-! ### Finite-dimensionality and the dimension estimate -/

section PrincipalDegree

variable (hDegreeZero : ∀ f : M.K, degree (pdiv f) = 0)
include hDegreeZero

#check hDegreeZero
#check @mem_L_of_ne_zero
#check @divisorDegree_nonneg

set_option pp.explicit true in
#check (fun f : M.K => hDegreeZero f)

theorem negativeSpace {A : Divisor M} (hA : degree A < 0) : L A = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  have hfzero : f = 0 := by
    by_contra hf0
    have hnonneg := divisorDegree_nonneg M ((mem_L_of_ne_zero M hDVR hf0).mp hf)
    have hadd := divisorDegree_add M A (functionDivisor M hDVR f)
    have hzero := hDegreeZero f
    change 0 ≤ divisorDegree M (A + functionDivisor M hDVR f) at hnonneg
    omega
  exact (Submodule.mem_bot ℚ).mpr hfzero


#print negativeSpace
#print axioms negativeSpace
end PrincipalDegree
end RiemannDimension
end AbcAdaptation.Tripod.Fermat.Proper
