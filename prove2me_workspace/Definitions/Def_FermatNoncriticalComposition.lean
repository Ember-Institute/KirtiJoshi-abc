/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Source proof: CurveField/Noncritical.lean:126-171 at pinned Belyi
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatNoncriticalSimpleZeros

set_option autoImplicit false

open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

open NoncriticalP1 (ElemMap zeroOneInf evalComp ramIdxComp compK)

variable {N : ℕ}

/-- All three inputs concern actual ramification or actual rational maps.
The source construction forms the finite Galois-stable set of all branch
values, including all residue embeddings, then uses the actual elementary
composite H and sets φ=H(ψ). -/
theorem noncriticalSelection_of_simpleZeros_and_children
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hSimple : ∀ T : Finset (Place M.K), Nonempty (SimpleZeroFunction M hDVR T))
    (hFiniteRam : ∀ ψ : M.K, Transcendental ℚ ψ →
      {P : Place M.K | 1 < ramIdx M hDVR ψ P}.Finite)
    (hCompose : ∀ ψ : M.K, Transcendental ℚ ψ →
      (∀ P : Place M.K, 0 < ramIdx M hDVR ψ P) ∧
      ∀ (hs : List ElemMap) (x : QbarPoint M.K),
        Transcendental ℚ (compK hs ψ) ∧
        noncriticalValue M x (compK hs ψ) = evalComp hs (noncriticalValue M x ψ) ∧
        ramIdx M hDVR (compK hs ψ) x.P =
          ramIdx M hDVR ψ x.P * (ramIdxComp hs (noncriticalValue M x ψ) : ℤ))
    (hP1 : ∀ S : Finset NoncriticalP1.Pt,
      (∀ σ : Tripod.Qbar ≃ₐ[ℚ] Tripod.Qbar, ∀ z ∈ S, z.map σ ∈ S) →
      some 0 ∉ S → ∃ hs : List ElemMap,
        (∀ z ∈ S, evalComp hs z ∈ zeroOneInf) ∧
        evalComp hs (some 0) ∉ zeroOneInf ∧
        (∀ z, 1 < ramIdxComp hs z → evalComp hs z ∈ zeroOneInf)) :
    NoncriticalSelection M hDVR := by
  classical
  letI : IsCurveField M.K := M.isCurveField
  intro T
  obtain ⟨F⟩ := hSimple T
  let ψ := F.ψ
  have hψ : Transcendental ℚ ψ := F.transcendental
  have hψ0 : ψ ≠ 0 := ne_zero_of_transcendental hψ
  have hR := hFiniteRam ψ hψ
  have hX := QbarPoint.noncritical_finite_setOf_mem hR
  let S : Finset NoncriticalP1.Pt :=
    insert none (hX.toFinset.image fun x => noncriticalValue M x ψ)
  have hmemS : ∀ x : QbarPoint M.K, 1 < ramIdx M hDVR ψ x.P →
      noncriticalValue M x ψ ∈ S := fun x hx =>
    Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨x, hX.mem_toFinset.mpr hx, rfl⟩)
  have hSgal : ∀ σ : Tripod.Qbar ≃ₐ[ℚ] Tripod.Qbar, ∀ z ∈ S, z.map σ ∈ S := by
    intro σ z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_insert_self _ _
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [← noncriticalValue_gal]
      exact hmemS (noncriticalGalPoint M σ x)
        (show 1 < ramIdx M hDVR ψ x.P from hX.mem_toFinset.mp hx)
  have hval0 : ∀ x : QbarPoint M.K, x.P ∈ F.T' →
      noncriticalValue M x ψ = some 0 := by
    intro x hx
    rw [noncriticalValue_zero_iff M hDVR x hψ0, F.simple _ hx]
    exact one_pos
  have hzero : (some 0 : NoncriticalP1.Pt) ∉ S := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · cases h
    · obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp h
      have hram : 1 < ramIdx M hDVR ψ x.P := hX.mem_toFinset.mp hx
      have hxpos := (noncriticalValue_zero_iff M hDVR x hψ0).mp hxv
      have hxT : x.P ∈ F.T' := by
        by_contra hn
        have := F.no_other_zeros _ hn
        change ord M hDVR x.P ψ ≤ 0 at this
        omega
      rw [noncritical_ramIdx_of_positive_order M hDVR ψ x.P hxpos,
        F.simple _ hxT] at hram
      exact lt_irrefl _ hram
  obtain ⟨hs, hmaps, hzeroGood, hunram⟩ := hP1 S hSgal hzero
  obtain ⟨P0, hP0⟩ := F.nonempty
  obtain ⟨x0, -⟩ := QbarPoint.noncritical_exists_P_eq (K := M.K) P0
  have hφ := ((hCompose ψ hψ).2 hs x0).1
  refine ⟨compK hs ψ, ⟨hφ, fun P hP => ?_⟩, fun P hPT => ?_⟩
  · obtain ⟨x, rfl⟩ := QbarPoint.noncritical_exists_P_eq (K := M.K) P
    obtain ⟨-, hv, he⟩ := (hCompose ψ hψ).2 hs x
    rw [noncritical_cusp_value_iff M hDVR _ hφ x, hv]
    rw [he] at hP
    by_cases h1 : 1 < ramIdx M hDVR ψ x.P
    · exact hmaps _ (hmemS x h1)
    · have hpos := (hCompose ψ hψ).1 x.P
      have h1' : ramIdx M hDVR ψ x.P = 1 := by omega
      rw [h1', one_mul] at hP
      exact hunram _ (by exact_mod_cast hP)
  · obtain ⟨x, rfl⟩ := QbarPoint.noncritical_exists_P_eq (K := M.K) P
    obtain ⟨-, hv, -⟩ := (hCompose ψ hψ).2 hs x
    rw [noncritical_cusp_value_iff M hDVR _ hφ x, hv, hval0 x (F.contains hPT)]
    exact hzeroGood

end AbcAdaptation.Tripod.Fermat.Proper
