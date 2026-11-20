/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Transport.lean
-/
import Solutions.Source_ReferenceIutCanLiftDeckGroup
import Mathlib.Algebra.Group.Action.End
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Tactic.Group

set_option autoImplicit false

open Filter Set Topology
open Matrix.SpecialLinearGroup (toGL)
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ComplexConjugate

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.IsUniformization

variable {W : WeierstrassCurve ℂ} {A B A₁ B₁ : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- Replacing the generators by a pair generating the same subgroup keeps the fibers. -/
theorem of_closure_eq (h : IsUniformization W A B π)
    (hEq : Subgroup.closure {A₁, B₁} = Subgroup.closure {A, B}) :
    IsUniformization W A₁ B₁ π :=
  ⟨h.holo, h.mem, h.surj, fun z w ↦ by rw [hEq, h.fibre z w]⟩

private theorem pmGroup_eq_sup (A B : SL(2, ℝ)) :
    pmGroup A B = Subgroup.closure {A, B} ⊔ Subgroup.closure {(-1 : SL(2, ℝ))} := by
  have h : ({A, B, -1} : Set SL(2, ℝ)) = ({A, B} : Set SL(2, ℝ)) ∪ {-1} := by
    ext γ
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  rw [pmGroup, h, Subgroup.closure_union]

/-- The signed group and the two generators have the same orbits on the upper half-plane. -/
private theorem pmGroup_orbit_iff (A B : SL(2, ℝ)) (z w : ℍ) :
    (∃ γ ∈ pmGroup A B, γ • z = w) ↔
      ∃ γ ∈ Subgroup.closure {A, B}, γ • z = w := by
  let act := MulAction.toPermHom SL(2, ℝ) ℍ
  have hneg : act (-1) = 1 := by
    apply Equiv.ext
    intro u
    change (-1 : SL(2, ℝ)) • u = u
    exact neg_one_act u
  have hmap : (pmGroup A B).map act = (Subgroup.closure {A, B}).map act := by
    simp only [pmGroup_eq_sup, Subgroup.map_sup, MonoidHom.map_closure, Set.image_singleton,
      hneg, Subgroup.closure_singleton_one, sup_bot_eq]
  constructor
  · rintro ⟨g, hg, hgzw⟩
    have hAct := Subgroup.mem_map_of_mem act hg
    rw [hmap] at hAct
    obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.mp hAct
    have hγz : γ • z = g • z := congrArg (fun f : Equiv.Perm ℍ ↦ f z) hγg
    exact ⟨γ, hγ, hγz.trans hgzw⟩
  · rintro ⟨g, hg, hgzw⟩
    exact ⟨g, closure_le_pmGroup A B hg, hgzw⟩

private theorem pmGroup_le_of_signs (hA : A₁ = A ∨ A₁ = -A) (hB : B₁ = B ∨ B₁ = -B) :
    pmGroup A₁ B₁ ≤ pmGroup A B := by
  have mem_sign {x y : SL(2, ℝ)} (hxy : y = x ∨ y = -x) (hx : x ∈ pmGroup A B) :
      y ∈ pmGroup A B := by
    rcases hxy with rfl | rfl
    · exact hx
    · simpa only [neg_one_mul] using mul_mem (neg_one_mem_pmGroup A B) hx
  rw [pmGroup, Subgroup.closure_le]
  intro γ hγ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl
  · exact mem_sign hA (closure_le_pmGroup A B (Subgroup.subset_closure (by simp)))
  · exact mem_sign hB (closure_le_pmGroup A B (Subgroup.subset_closure (by simp)))
  · exact neg_one_mem_pmGroup A B

/-- Changing the signs of the generators keeps the fibers because `-1` acts trivially. -/
theorem of_signs (h : IsUniformization W A B π)
    (hA : A₁ ∈ ({A, -A} : Set SL(2, ℝ))) (hB : B₁ ∈ ({B, -B} : Set SL(2, ℝ))) :
    IsUniformization W A₁ B₁ π := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
  have hAr : A = A₁ ∨ A = -A₁ := by
    rcases hA with rfl | rfl <;> simp
  have hBr : B = B₁ ∨ B = -B₁ := by
    rcases hB with rfl | rfl <;> simp
  have hpm : pmGroup A₁ B₁ = pmGroup A B :=
    le_antisymm (pmGroup_le_of_signs hA hB) (pmGroup_le_of_signs hAr hBr)
  refine ⟨h.holo, h.mem, h.surj, fun z w ↦ ?_⟩
  rw [h.fibre z w, ← pmGroup_orbit_iff A B z w, ← pmGroup_orbit_iff A₁ B₁ z w, hpm]

private theorem sl_smul_eq_toGL (γ : SL(2, ℝ)) (z : ℍ) : γ • z = toGL γ • z := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, coe_smul_of_det_pos (by simp)]
  simp [num, denom]

private theorem exists_conj_mem {g : GL (Fin 2) ℝ}
    (hA : g * toGL A * g⁻¹ = toGL A₁) (hB : g * toGL B * g⁻¹ = toGL B₁) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {A, B}) :
    ∃ γ₁ ∈ Subgroup.closure {A₁, B₁}, toGL γ₁ = g * toGL γ * g⁻¹ := by
  let f := (MulAut.conj g).toMonoidHom.comp (toGL : SL(2, ℝ) →* GL (Fin 2) ℝ)
  have hmap : (Subgroup.closure {A, B}).map f = (Subgroup.closure {A₁, B₁}).map toGL := by
    simp only [MonoidHom.map_closure, Set.image_pair]
    change Subgroup.closure {g * toGL A * g⁻¹, g * toGL B * g⁻¹} =
      Subgroup.closure {toGL A₁, toGL B₁}
    rw [hA, hB]
  have hmem := Subgroup.mem_map_of_mem f hγ
  rw [hmap] at hmem
  exact Subgroup.mem_map.mp hmem

private theorem orbits_conj {g : GL (Fin 2) ℝ}
    (hA : g * toGL A * g⁻¹ = toGL A₁) (hB : g * toGL B * g⁻¹ = toGL B₁) (z w : ℍ) :
    (∃ γ ∈ Subgroup.closure {A, B}, γ • (g⁻¹ • z) = g⁻¹ • w) ↔
      ∃ γ₁ ∈ Subgroup.closure {A₁, B₁}, γ₁ • z = w := by
  have hA' : g⁻¹ * toGL A₁ * g⁻¹⁻¹ = toGL A := by rw [← hA]; group
  have hB' : g⁻¹ * toGL B₁ * g⁻¹⁻¹ = toGL B := by rw [← hB]; group
  constructor
  · rintro ⟨γ, hγ, e⟩
    obtain ⟨γ₁, h₁, e₁⟩ := exists_conj_mem hA hB hγ
    exact ⟨γ₁, h₁, by
      rw [sl_smul_eq_toGL, e₁, mul_smul, mul_smul, ← sl_smul_eq_toGL, e, smul_inv_smul]⟩
  · rintro ⟨γ₁, h₁, e⟩
    obtain ⟨γ, hγ, eγ⟩ := exists_conj_mem hA' hB' h₁
    exact ⟨γ, hγ, by
      rw [sl_smul_eq_toGL, eγ, mul_smul, mul_smul, inv_inv, smul_inv_smul, ← sl_smul_eq_toGL, e]⟩

private noncomputable def mobC (g : GL (Fin 2) ℝ) (u : ℂ) : ℂ :=
  num g u / denom g u

private theorem hasDerivAt_mobC (g : GL (Fin 2) ℝ) {u : ℂ} (hu : u.im ≠ 0) :
    HasDerivAt (mobC g) (g.det.val / denom g u ^ 2) u := by
  have hnum : HasDerivAt (num g) (g 0 0) u := by
    have h := ((hasDerivAt_id' u).const_mul ((g 0 0 : ℝ) : ℂ)).add_const ((g 0 1 : ℝ) : ℂ)
    rwa [mul_one] at h
  have hdenom : HasDerivAt (denom g) (g 1 0) u := by
    have h := ((hasDerivAt_id' u).const_mul ((g 1 0 : ℝ) : ℂ)).add_const ((g 1 1 : ℝ) : ℂ)
    rwa [mul_one] at h
  refine (hnum.div hdenom (denom_ne_zero_of_im g hu)).congr_deriv ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [num, denom]
  push_cast
  ring

private theorem mobC_derivative_ne_zero (g : GL (Fin 2) ℝ) {u : ℂ} (hu : u.im ≠ 0) :
    (g.det.val : ℂ) / denom g u ^ 2 ≠ 0 :=
  div_ne_zero (by exact_mod_cast g.det.ne_zero) (pow_ne_zero _ (denom_ne_zero_of_im g hu))

private theorem coe_smul_ofComplex {g : GL (Fin 2) ℝ} {u : ℂ} (hu : 0 < u.im) :
    ((g • ofComplex u : ℍ) : ℂ) = σ g (mobC g u) := by
  rw [UpperHalfPlane.coe_smul, ofComplex_apply_of_im_pos hu]
  rfl

/-- A real conjugation of positive determinant transports the uniformization on the same curve. -/
theorem conj_pos (h : IsUniformization W A B π) {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    (hA : g * toGL A * g⁻¹ = toGL A₁) (hB : g * toGL B * g⁻¹ = toGL B₁) :
    ∃ π' : ℂ → ℂ × ℂ, IsUniformization W A₁ B₁ π' := by
  have hgi : 0 < (g⁻¹ : GL (Fin 2) ℝ).det.val := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hg
  let π' : ℂ → ℂ × ℂ := fun u ↦ π ((g⁻¹ • ofComplex u : ℍ) : ℂ)
  refine ⟨π', ?_, ?_, ?_, ?_⟩
  · intro z
    have heq : π' =ᶠ[𝓝 (z : ℂ)] π ∘ mobC g⁻¹ := by
      filter_upwards [isOpen_upper.mem_nhds z.im_pos] with u hu
      have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := hg
      simp [π', coe_smul_ofComplex hu, σ, hg']
    have hm : ((g⁻¹ • z : ℍ) : ℂ) = mobC g⁻¹ z := coe_smul_of_det_pos hgi z
    have hc := (h.hasDerivAt (g⁻¹ • z)).scomp_of_eq (z : ℂ)
      (hasDerivAt_mobC g⁻¹ z.im_ne_zero) hm
    refine ⟨(hc.congr_of_eventuallyEq heq).differentiableAt, ?_⟩
    rw [heq.deriv_eq, hc.deriv]
    exact smul_ne_zero (mobC_derivative_ne_zero g⁻¹ z.im_ne_zero) (h.holo (g⁻¹ • z)).2
  · intro z
    simpa only [π', ofComplex_apply] using h.mem (g⁻¹ • z)
  · intro x y hxy
    obtain ⟨z, hz⟩ := h.surj x y hxy
    exact ⟨g • z, by simp only [π', ofComplex_apply, inv_smul_smul, hz]⟩
  · intro z w
    simp only [π', ofComplex_apply]
    rw [h.fibre, orbits_conj hA hB]

private noncomputable def conjugateCoordinates (p : ℂ × ℂ) : ℂ × ℂ :=
  (conj p.1, conj p.2)

private theorem conjugateCoordinates_involutive : Function.Involutive conjugateCoordinates := by
  rintro ⟨x, y⟩
  simp [conjugateCoordinates]

private theorem hasDerivAt_conj_prod {p : ℂ × ℂ} {v : ℂ} (h : HasDerivAt π p (conj v)) :
    HasDerivAt (fun u ↦ conjugateCoordinates (π (conj u))) (conjugateCoordinates p) v := by
  have hfst : HasDerivAt (fun u ↦ (π u).1) p.1 (conj v) :=
    (hasFDerivAt_fst (p := π (conj v))).comp_hasDerivAt (conj v) h
  have hsnd : HasDerivAt (fun u ↦ (π u).2) p.2 (conj v) :=
    (hasFDerivAt_snd (p := π (conj v))).comp_hasDerivAt (conj v) h
  have h₁ := hfst.conj_conj
  have h₂ := hsnd.conj_conj
  rw [Complex.conj_conj] at h₁ h₂
  exact h₁.prodMk h₂

/-- A real conjugation of negative determinant transports the uniformization to the
complex-conjugate curve. -/
theorem conj_neg (h : IsUniformization W A B π) {g : GL (Fin 2) ℝ} (hg : g.det.val < 0)
    (hA : g * toGL A * g⁻¹ = toGL A₁) (hB : g * toGL B * g⁻¹ = toGL B₁) :
    ∃ π' : ℂ → ℂ × ℂ, IsUniformization (W.map (starRingEnd ℂ)) A₁ B₁ π' := by
  have hgi : (g⁻¹ : GL (Fin 2) ℝ).det.val < 0 := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact inv_lt_zero.mpr hg
  have hg' : (g : Matrix (Fin 2) (Fin 2) ℝ).det < 0 := hg
  have hσ (v : ℂ) : σ g⁻¹ v = conj v := by simp [σ, hg'.not_gt]
  let π' : ℂ → ℂ × ℂ := fun u ↦ conjugateCoordinates (π ((g⁻¹ • ofComplex u : ℍ) : ℂ))
  let Pc : ℂ → ℂ × ℂ := fun u ↦ conjugateCoordinates (π (conj u))
  refine ⟨π', ?_, ?_, ?_, ?_⟩
  · intro z
    have heq : π' =ᶠ[𝓝 (z : ℂ)] Pc ∘ mobC g⁻¹ := by
      filter_upwards [isOpen_upper.mem_nhds z.im_pos] with u hu
      simp only [π', Pc, Function.comp_def, coe_smul_ofComplex hu, hσ]
    have hm : ((g⁻¹ • z : ℍ) : ℂ) = conj (mobC g⁻¹ z) := by
      calc
        ((g⁻¹ • z : ℍ) : ℂ) = σ g⁻¹ (mobC g⁻¹ z) := rfl
        _ = conj (mobC g⁻¹ z) := hσ _
    have hπ := h.hasDerivAt (g⁻¹ • z)
    rw [hm] at hπ
    have hPc : HasDerivAt Pc (conjugateCoordinates (deriv π (conj (mobC g⁻¹ z))))
        (mobC g⁻¹ z) := hasDerivAt_conj_prod hπ
    have hc := hPc.scomp (z : ℂ) (hasDerivAt_mobC g⁻¹ z.im_ne_zero)
    have hdP : conjugateCoordinates (deriv π (conj (mobC g⁻¹ z))) ≠ 0 := by
      intro hzero
      apply (h.holo (g⁻¹ • z)).2
      rw [hm]
      exact conjugateCoordinates_involutive.injective
        (hzero.trans (by simp [conjugateCoordinates]; rfl))
    refine ⟨(hc.congr_of_eventuallyEq heq).differentiableAt, ?_⟩
    rw [heq.deriv_eq, hc.deriv]
    exact smul_ne_zero (mobC_derivative_ne_zero g⁻¹ z.im_ne_zero) hdP
  · intro z
    simp only [π', ofComplex_apply, conjugateCoordinates]
    exact (WeierstrassCurve.Affine.map_equation W.toAffine (f := starRingEnd ℂ)
      (RingHom.injective _) _ _).mpr (h.mem (g⁻¹ • z))
  · intro x y hxy
    have hxy' : W.toAffine.Equation (conj x) (conj y) :=
      (WeierstrassCurve.Affine.map_equation W.toAffine (f := starRingEnd ℂ)
        (RingHom.injective _) (conj x) (conj y)).mp
        (by simpa only [Complex.conj_conj] using hxy)
    obtain ⟨z, hz⟩ := h.surj _ _ hxy'
    exact ⟨g • z, by
      simp only [π', ofComplex_apply, inv_smul_smul, hz, conjugateCoordinates, Complex.conj_conj]⟩
  · intro z w
    simp only [π', ofComplex_apply]
    rw [conjugateCoordinates_involutive.injective.eq_iff, h.fibre, orbits_conj hA hB]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.IsUniformization
