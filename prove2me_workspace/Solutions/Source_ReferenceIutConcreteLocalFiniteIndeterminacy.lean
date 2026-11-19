/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/LocalConstruct/Indeterminacy.lean and
  Iut/Concrete/LocalConstruct/ThetaAdmissible.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalFiniteHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndeterminacy

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open MeasureTheory NumberField
open scoped Pointwise

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

/-- Conjugate an endomorphism of the actual completion tensor by the packet equivalence. -/
def genuineTensorConjugate (hc : ∀ j, IsOver K p (c j))
    (φ : (genuinePacket p c hc).Tensor → (genuinePacket p c hc).Tensor) :
    Tensor K (.finite p) c → Tensor K (.finite p) c :=
  fun x => genuineTensorEquiv p c hc (φ ((genuineTensorEquiv p c hc).symm x))

theorem genuineTensorConjugate_image (hc : ∀ j, IsOver K p (c j))
    (φ : (genuinePacket p c hc).Tensor → (genuinePacket p c hc).Tensor)
    (S : Set (genuinePacket p c hc).Tensor) :
    genuineTensorConjugate p c hc φ '' (genuineTensorEquiv p c hc '' S) =
      genuineTensorEquiv p c hc '' (φ '' S) := by
  let e := genuineTensorEquiv p c hc
  change (fun x => e (φ (e.symm x))) '' (e '' S) = e '' (φ '' S)
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr' fun x => by rw [e.symm_apply_apply]

open Classical in
/-- The transported completion-factor automorphisms. The zero-ring packet has one map. -/
def finiteIndAut : Set (Tensor K (.finite p) c → Tensor K (.finite p) c) :=
  if hc : ∀ j, IsOver K p (c j) then
    genuineTensorConjugate p c hc '' (genuinePacket p c hc).factorIndeterminacies
  else {id}

theorem finiteIndAut_eq_image_of_isOver (hc : ∀ j, IsOver K p (c j)) :
    finiteIndAut p c =
      genuineTensorConjugate p c hc '' (genuinePacket p c hc).factorIndeterminacies := by
  rw [finiteIndAut, dif_pos hc]

theorem id_mem_finiteIndAut : id ∈ finiteIndAut p c := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [finiteIndAut_eq_image_of_isOver p c hc]
    exact ⟨id, (genuinePacket p c hc).id_mem_factorIndeterminacies,
      funext fun x => (genuineTensorEquiv p c hc).apply_symm_apply x⟩
  · simp only [finiteIndAut, dif_neg hc, Set.mem_singleton_iff]

private theorem finiteIndAut_finite : (finiteIndAut p c).Finite := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [finiteIndAut_eq_image_of_isOver p c hc]
    exact (genuinePacket p c hc).factorIndeterminacies_finite.image _
  · rw [finiteIndAut, dif_neg hc]
    exact Set.finite_singleton id

theorem finiteIndAut_exists_algEquiv {φ : Tensor K (.finite p) c → Tensor K (.finite p) c}
    (hφ : φ ∈ finiteIndAut p c) :
    ∃ σ : Tensor K (.finite p) c ≃ₐ[ℚ_[p]] Tensor K (.finite p) c, φ = ⇑σ := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [finiteIndAut_eq_image_of_isOver p c hc] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    obtain ⟨σ, rfl⟩ := hψ
    let P := genuinePacket p c hc
    let e := genuineTensorEquiv p c hc
    exact ⟨(e.symm.trans (P.factorTensorAut σ)).trans e, rfl⟩
  · rw [finiteIndAut, dif_neg hc, Set.mem_singleton_iff] at hφ
    subst φ
    exact ⟨AlgEquiv.refl, rfl⟩

private theorem continuous_of_mem_finiteIndAut {φ : Tensor K (.finite p) c → Tensor K (.finite p) c}
    (hφ : φ ∈ finiteIndAut p c) : Continuous φ := by
  obtain ⟨σ, rfl⟩ := finiteIndAut_exists_algEquiv p c hφ
  exact σ.toLinearMap.continuous_of_finiteDimensional

/-- The finite orbit of a compact region of positive Haar mass is admissible. -/
theorem iUnion_finiteIndAut_admissible {S : Set (Tensor K (.finite p) c)}
    (hS : IsCompact S) (hpos : 0 < finiteHaar p c S) :
    (⋃ φ ∈ finiteIndAut p c, φ '' S) ∈ finiteAdmissible p c := by
  let orbit := ⋃ φ ∈ finiteIndAut p c, φ '' S
  have hsub : S ⊆ orbit := fun x hx =>
    Set.mem_iUnion₂.mpr ⟨id, id_mem_finiteIndAut p c, ⟨x, hx, rfl⟩⟩
  have hc : IsCompact orbit :=
    (finiteIndAut_finite p c).isCompact_biUnion fun φ hφ =>
      hS.image (continuous_of_mem_finiteIndAut p c hφ)
  have hmass : 0 < finiteHaar p c orbit := hpos.trans_le (measure_mono hsub)
  exact ⟨nonempty_of_measure_ne_zero hmass.ne', hc.isClosed.closure_eq.symm ▸ hc,
    hc.isClosed.measurableSet, hmass, hc.measure_lt_top⟩

theorem theta_admissible_finite (a : Tensor K (.finite p) c) (ha : IsUnit a) :
    (⋃ φ ∈ finiteIndAut p c, φ '' (a • integral p c)) ∈ finiteAdmissible p c :=
  iUnion_finiteIndAut_admissible p c (isCompact_smul_integral p c a)
    (finiteHaar_smul_integral_pos p c ha)

/-- Proposition 1.4(iv) for the maximal order in the finite packet. -/
theorem prop14_iv :
    ∀ φ ∈ finiteIndAut p c, φ '' integral p c ⊆ integral p c := by
  intro φ hφ
  obtain ⟨σ, rfl⟩ := finiteIndAut_exists_algEquiv p c hφ
  rintro _ ⟨x, hx, rfl⟩
  change IsIntegral ℤ_[p] (σ x)
  exact IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) σ.toRingHom
    (RingHom.ext fun r => (σ.commutes (r : ℚ_[p])).symm) hx

end

end AbcAdaptation.Reference.Iut.LocalConstruct
