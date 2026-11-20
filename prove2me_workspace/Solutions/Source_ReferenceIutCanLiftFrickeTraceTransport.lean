/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Mathlib.GroupTheory.Commensurable
import Solutions.Source_ReferenceIutCanLiftComplexFromModelUniformizations
import Solutions.Source_ReferenceIutCanLiftDeckGroup
import Solutions.Source_ReferenceIutCanLiftDenseCriterion
import Solutions.Source_ReferenceIutCanLiftFrickeNormalForm

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke (tr nA nB exists_normal_form)
open IsUniformization (pmGroup closure_le_pmGroup neg_one_mem_pmGroup relIndex_closure_pmGroup_ne_zero)
open Subgroup.Commensurable (commensurator commensurator_mem_iff)

/-- The arithmetic integrality input on positive Fricke normal forms. -/
def NormalFormTraceIntegrality : Prop :=
  ∀ {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z),
    0 < x → 0 < y → x < y + z → y < x + z → z < x + y →
    Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ)) →
    ∀ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}, ∃ m : ℤ, tr γ ^ 2 = m

private theorem relIndex_ne_zero_of_signs {A B A' B' : SL(2, ℝ)}
    (hA : A' ∈ ({A, -A} : Set SL(2, ℝ))) (hB : B' ∈ ({B, -B} : Set SL(2, ℝ))) :
    (Subgroup.closure {A, B}).relIndex (Subgroup.closure {A', B'}) ≠ 0 := by
  have mem_of_sign {X Y : SL(2, ℝ)} (hX : X ∈ pmGroup A B)
      (hY : Y ∈ ({X, -X} : Set SL(2, ℝ))) : Y ∈ pmGroup A B := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
    rcases hY with rfl | rfl
    · exact hX
    · simpa only [neg_one_mul] using mul_mem (neg_one_mem_pmGroup A B) hX
  have hle : Subgroup.closure {A', B'} ≤ pmGroup A B := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨mem_of_sign (closure_le_pmGroup A B (Subgroup.subset_closure (by simp))) hA,
      mem_of_sign (closure_le_pmGroup A B (Subgroup.subset_closure (by simp))) hB⟩
  exact Subgroup.relIndex_ne_zero_trans (relIndex_closure_pmGroup_ne_zero A B)
    (by rw [Subgroup.relIndex_eq_one.mpr hle]; exact one_ne_zero)

private theorem commensurable_of_signs {A B A' B' : SL(2, ℝ)}
    (hA : A' ∈ ({A, -A} : Set SL(2, ℝ))) (hB : B' ∈ ({B, -B} : Set SL(2, ℝ))) :
    Subgroup.Commensurable (Subgroup.closure {A', B'}) (Subgroup.closure {A, B}) := by
  have reverse_sign {X Y : SL(2, ℝ)} (h : Y ∈ ({X, -X} : Set SL(2, ℝ))) :
      X ∈ ({Y, -Y} : Set SL(2, ℝ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl <;> simp
  exact ⟨relIndex_ne_zero_of_signs (reverse_sign hA) (reverse_sign hB),
    relIndex_ne_zero_of_signs hA hB⟩

private theorem mem_or_neg_mem_of_signs {A B A' B' γ : SL(2, ℝ)}
    (hA : A' ∈ ({A, -A} : Set SL(2, ℝ))) (hB : B' ∈ ({B, -B} : Set SL(2, ℝ)))
    (hγ : γ ∈ Subgroup.closure {A, B}) :
    γ ∈ Subgroup.closure {A', B'} ∨ -γ ∈ Subgroup.closure {A', B'} := by
  let Γ := Subgroup.closure {A', B'}
  have hA' : A' ∈ Γ := Subgroup.subset_closure (by simp)
  have hB' : B' ∈ Γ := Subgroup.subset_closure (by simp)
  have original_mem {X Y : SL(2, ℝ)} (h : Y ∈ ({X, -X} : Set SL(2, ℝ)))
      (hY : Y ∈ Γ) : X ∈ Γ ∨ -X ∈ Γ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact Or.inl hY
    · exact Or.inr hY
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact original_mem hA hA'
    · exact original_mem hB hB'
  | one => exact Or.inl (one_mem _)
  | mul g h _ _ hg hh =>
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · exact Or.inl (mul_mem hg hh)
    · exact Or.inr (by simpa only [mul_neg] using mul_mem hg hh)
    · exact Or.inr (by simpa only [neg_mul] using mul_mem hg hh)
    · exact Or.inl (by simpa only [neg_mul_neg] using mul_mem hg hh)
  | inv g _ hg =>
    rcases hg with hg | hg
    · exact Or.inl (inv_mem hg)
    · exact Or.inr (by simpa using inv_mem hg)

private theorem mem_commensurator_map_iff {G : Type*} [Group G] (H : Subgroup G)
    (f : G →* G) (hf : Function.Injective f) (γ : G) :
    f γ ∈ commensurator (H.map f) ↔ γ ∈ commensurator H := by
  have hconj : ConjAct.toConjAct (f γ) • (H.map f) = (ConjAct.toConjAct γ • H).map f := by
    have hsmul (x : G) :
        ConjAct.toConjAct (f γ) • f x = f (ConjAct.toConjAct γ • x) := by
      simp only [ConjAct.toConjAct_smul, map_mul, map_inv]
    ext δ
    constructor
    · intro hδ
      obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hδ
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨ConjAct.toConjAct γ • x,
        Subgroup.smul_mem_pointwise_smul _ _ _ hx, (hsmul x).symm⟩
    · intro hδ
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hδ
      obtain ⟨x, hx, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hy
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨f x, Subgroup.mem_map_of_mem f hx, hsmul x⟩
  rw [commensurator_mem_iff, commensurator_mem_iff, hconj]
  simp only [Subgroup.Commensurable, Subgroup.relIndex_map_map_of_injective _ _ hf]

/-- Transport the normal-form integrality input to the original generating pair. -/
theorem trace_sq_int_of_dense_of_normalForm (hNormal : NormalFormTraceIntegrality)
    {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0)
    (hDense : Dense (commensurator (Subgroup.closure {A, B}) : Set SL(2, ℝ))) :
    ∀ γ ∈ Subgroup.closure {A, B}, ∃ m : ℤ, tr γ ^ 2 = m := by
  obtain ⟨x, y, z, hx, hy, hz, hrel, ⟨tx, ty, tz⟩, A', B', hcl, A'', hA'', B'', hB'', g, hgA, hgB⟩ :=
    exists_normal_form hcomm hA
  let H := Subgroup.closure {A'', B''}
  let Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  have hCommeq : commensurator H = commensurator (Subgroup.closure {A, B}) := by
    rw [← hcl]
    exact (commensurable_of_signs hA'' hB'').eq
  let P : Matrix (Fin 2) (Fin 2) ℝ := g
  have hP : IsUnit P.det := g.isUnit.map Matrix.detMonoidHom
  let φ := SL2R.conjMat P hP
  let φHomeo := SL2R.conjHomeo P hP
  have hφ (C D : SL(2, ℝ)) (h : g * toGL C * g⁻¹ = toGL D) : φ C = D := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    simpa only [Units.val_mul, coe_GL_coe_matrix, Matrix.coe_units_inv, P] using
      congrArg Units.val h
  have hΓ : Γ = H.map φ := by
    change Subgroup.closure {nA hz hrel, nB hz hrel} = (Subgroup.closure {A'', B''}).map φ
    rw [MonoidHom.map_closure, Set.image_pair, hφ _ _ hgA, hφ _ _ hgB]
  have hDense' : Dense (commensurator H : Set SL(2, ℝ)) := by rwa [hCommeq]
  have hDenseImage : Dense (φHomeo '' (commensurator H : Set SL(2, ℝ))) :=
    φHomeo.surjective.denseRange.dense_image φHomeo.continuous hDense'
  have hDenseΓ : Dense (commensurator Γ : Set SL(2, ℝ)) := by
    apply hDenseImage.mono
    rintro _ ⟨γ, hγ, rfl⟩
    change φ γ ∈ commensurator Γ
    rw [hΓ]
    exact (mem_commensurator_map_iff H φ φHomeo.injective γ).mpr hγ
  have hInt (δ : SL(2, ℝ)) (hδ : δ ∈ H) : ∃ m : ℤ, tr δ ^ 2 = m := by
    have hφδ : φ δ ∈ Γ := by
      rw [hΓ]
      exact Subgroup.mem_map_of_mem φ hδ
    obtain ⟨m, hm⟩ := hNormal hz hrel hx hy tx ty tz hDenseΓ (φ δ) hφδ
    exact ⟨m, by rw [← hm, SL2R.tr_conjMat]⟩
  intro γ hγ
  have hγ' : γ ∈ Subgroup.closure {A', B'} := by rwa [hcl]
  rcases mem_or_neg_mem_of_signs hA'' hB'' hγ' with h | h
  · exact hInt γ h
  · obtain ⟨m, hm⟩ := hInt (-γ) h
    exact ⟨m, by simpa only [tr, coe_neg, trace_neg, neg_sq] using hm⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

namespace AbcAdaptation.Reference.Iut.Anabelian

open CanLiftAnalytic CanLiftAnalytic.Takeuchi

/-- The arithmetic input on Fricke normal forms suffices for the actual lattice groups
in the complex CanLift assembly. -/
theorem canLift27Complex_of_fricke_normal_form
    (hNormal : M2.NormalFormTraceIntegrality)
    (hModels : ∀ k, ∃ i, Uniformizes (ccurve k) (takeuchiPair i) ∨
      Uniformizes ((ccurve k).map (starRingEnd ℂ)) (takeuchiPair i)) :
    CanLift27Complex :=
  canLift27Complex_of_model_uniformizations
    (fun U ↦ M2.trace_sq_int_of_dense_of_normalForm hNormal
      (Peripheral.trace_commutator U) (Peripheral.trace_A_ne_zero U)) hModels

end AbcAdaptation.Reference.Iut.Anabelian
