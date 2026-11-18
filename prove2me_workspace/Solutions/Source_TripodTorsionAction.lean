/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/-
Original repository https://github.com/lana-agents/iut
Original path Iut/Tripod/TorsionDegree.lean
The coordinate membership lemma comes from Iut/Tripod/CurveOf.lean.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData
import Mathlib.Algebra.Module.Torsion.Basic

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve
open scoped Classical

section GaloisAction

variable (K : IntermediateField ℚ Qbar) {l : Qbar} (hl : l ∈ K)

/-- The Legendre curve `E_λ` as a curve over a subfield `K ∋ λ` of `ℚ̄`. -/
noncomputable def legendreOver : WeierstrassCurve K := legendre (⟨l, hl⟩ : K)

/-- The action of `σ ∈ Gal(ℚ̄/K)` on `E_λ(ℚ̄)`: the functorial map of nonsingular points along
`σ : ℚ̄ →ₐ[K] ℚ̄`, for the model `E_λ/K`. -/
noncomputable def galAct (σ : Qbar ≃ₐ[K] Qbar) :
    (legendre l).toAffine.Point →+ (legendre l).toAffine.Point :=
  Affine.Point.map (W' := legendreOver K hl) (S := K) σ.toAlgHom

theorem galAct_one (P : (legendre l).toAffine.Point) : galAct K hl 1 P = P := by
  cases P <;> rfl

theorem galAct_mul (σ τ : Qbar ≃ₐ[K] Qbar) (P : (legendre l).toAffine.Point) :
    galAct K hl (σ * τ) P = galAct K hl σ (galAct K hl τ P) := by
  cases P <;> rfl

/-- The Galois action preserves the `n`-torsion. -/
theorem galAct_torsionBy (σ : Qbar ≃ₐ[K] Qbar) {n : ℕ} {P : (legendre l).toAffine.Point}
    (hP : P ∈ AddSubgroup.torsionBy (legendre l).toAffine.Point n) :
    galAct K hl σ P ∈ AddSubgroup.torsionBy (legendre l).toAffine.Point n := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

/-- The action of `σ ∈ Gal(ℚ̄/K)` on the `n`-torsion `E_λ(ℚ̄)[n]`. -/
noncomputable def galTorsion (n : ℕ) (σ : Qbar ≃ₐ[K] Qbar) :
    AddSubgroup.torsionBy (legendre l).toAffine.Point n →+
      AddSubgroup.torsionBy (legendre l).toAffine.Point n :=
  ((galAct K hl σ).domRestrict (AddSubgroup.torsionBy (legendre l).toAffine.Point n)).codRestrict
    (AddSubgroup.torsionBy (legendre l).toAffine.Point n)
    (fun P => galAct_torsionBy K hl σ P.2)

theorem mem_torsionCoords {l : Qbar} {n : ℕ} {P : (legendre l).toAffine.Point}
    (hP : n • P = 0) {c : Qbar} (hc : c ∈ coords P) : c ∈ torsionCoords l n :=
  Set.mem_biUnion (x := P) hP hc

/-- **`σ` fixes the `n`-torsion points iff it fixes their coordinates.** -/
theorem galAct_torsion_fixed_iff (σ : Qbar ≃ₐ[K] Qbar) (n : ℕ) :
    (∀ P : AddSubgroup.torsionBy (legendre l).toAffine.Point n, galAct K hl σ P = P) ↔
      ∀ c ∈ torsionCoords l n, σ c = c := by
  constructor
  · intro h c hc
    obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hc
    have hP' : P ∈ AddSubgroup.torsionBy (legendre l).toAffine.Point n :=
      AddSubgroup.torsionBy.nsmul_iff.mpr hP
    have hfix := h ⟨P, hP'⟩
    cases P with
    | zero => exact absurd hcP id
    | some x y hxy =>
      replace hfix := Affine.Point.some.inj
        (show Affine.Point.some (σ x) (σ y) _ = Affine.Point.some x y hxy from hfix)
      rcases hcP with rfl | rfl
      · exact hfix.1
      · exact hfix.2
  · rintro h ⟨P, hP⟩
    cases P with
    | zero => rfl
    | some x y hxy =>
      have hP' : n • Affine.Point.some x y hxy = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hP
      have hx : x ∈ coords (Affine.Point.some x y hxy) := by simp [coords]
      have hy : y ∈ coords (Affine.Point.some x y hxy) := by simp [coords]
      show Affine.Point.some (σ x) (σ y) _ = Affine.Point.some x y hxy
      exact (Eq.to_iff (Affine.Point.some.injEq ..)).2
        ⟨h x (mem_torsionCoords hP' hx), h y (mem_torsionCoords hP' hy)⟩

end GaloisAction

end AbcAdaptation.Tripod
