/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 2d8f000457da6447fa4df4bfec7365c1a49b6384
Original path Iut/Tripod/TameTwo.lean
-/
import Solutions.Source_ReferenceIutTowerInertiaInvolution
import Solutions.Source_TripodInertiaTransport
import Solutions.Source_TripodUnramified
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.ValuationTransfer
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine
open JoshiTeich.Act1Scene1.ReductionKernel (valuation_natCast_le_one)
open scoped Classical

section Models

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) (w : FinitePlace F)

/-- Integrality of a Weierstrass model over the completed integers gives integrality
for the valuation of the finite place. -/
private lemma isIntegralModel_of_baseChange
    [(E.baseChange (localCompletion w)).IsIntegral (w.maximalIdeal.adicCompletionIntegers F)] :
    IsIntegralModel (w.maximalIdeal.valuation F) E := by
  have h₁ := JoshiTeich.ReferenceIut.norm_a₁_le_one (E.baseChange (localCompletion w))
  have h₂ := JoshiTeich.ReferenceIut.norm_a₂_le_one (E.baseChange (localCompletion w))
  have h₃ := JoshiTeich.ReferenceIut.norm_a₃_le_one (E.baseChange (localCompletion w))
  have h₄ := JoshiTeich.ReferenceIut.norm_a₄_le_one (E.baseChange (localCompletion w))
  have h₆ := JoshiTeich.ReferenceIut.norm_a₆_le_one (E.baseChange (localCompletion w))
  rw [baseChange_adicCompletion_eq, map_a₁, norm_emb_le_one_iff] at h₁
  rw [baseChange_adicCompletion_eq, map_a₂, norm_emb_le_one_iff] at h₂
  rw [baseChange_adicCompletion_eq, map_a₃, norm_emb_le_one_iff] at h₃
  rw [baseChange_adicCompletion_eq, map_a₄, norm_emb_le_one_iff] at h₄
  rw [baseChange_adicCompletion_eq, map_a₆, norm_emb_le_one_iff] at h₆
  exact ⟨h₁, h₂, h₃, h₄, h₆⟩

/-- At a place of stable reduction, a global change of variables gives an integral
model with unit discriminant or unit c₄. -/
private theorem exists_integralModel_of_hasStableReductionAt (h : HasStableReductionAt E w) :
    ∃ C : VariableChange F, IsIntegralModel (w.maximalIdeal.valuation F) (C • E) ∧
      (w.maximalIdeal.valuation F (C • E).Δ = 1 ∨ w.maximalIdeal.valuation F (C • E).c₄ = 1) := by
  rcases h with ⟨C, hC⟩ | hm
  · letI := hC
    refine ⟨C, isIntegralModel_of_baseChange (C • E) w, Or.inl ?_⟩
    have hΔ : ‖((C • E).baseChange (localCompletion w)).Δ‖ = 1 :=
      (valuation_eq_one_iff w _).1 HasGoodReduction.goodReduction
    rwa [baseChange_adicCompletion_eq, map_Δ, JoshiTeich.ReferenceIut.norm_emb_eq_one_iff] at hΔ
  · obtain ⟨C, hC, hc₄, _⟩ := exists_variableChange_of_mult E w hm
    letI := hC
    exact ⟨C, isIntegralModel_of_baseChange (C • E) w, Or.inr hc₄⟩

end Models

section BaseChange

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {v : FinitePlace K} {w : FinitePlace k}

/-- An integral model remains integral at a place above the base place. -/
private lemma isIntegralModel_baseChange {W : WeierstrassCurve k}
    (hvw : FinitePlace.LiesOver v w) (h : IsIntegralModel (w.maximalIdeal.valuation k) W) :
    IsIntegralModel (v.maximalIdeal.valuation K) (W.map (algebraMap k K)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := h
  exact ⟨(JoshiTeich.ReferenceIut.valuation_algebraMap_le_one_iff hvw _).2 h₁,
    (JoshiTeich.ReferenceIut.valuation_algebraMap_le_one_iff hvw _).2 h₂,
    (JoshiTeich.ReferenceIut.valuation_algebraMap_le_one_iff hvw _).2 h₃,
    (JoshiTeich.ReferenceIut.valuation_algebraMap_le_one_iff hvw _).2 h₄,
    (JoshiTeich.ReferenceIut.valuation_algebraMap_le_one_iff hvw _).2 h₆⟩

/-- An inertia involution fixes odd prime-to-residue-characteristic torsion at a place
of stable reduction with residue characteristic 2. -/
private theorem torsion_fixed_by_inertia_involution
    (hvw : FinitePlace.LiesOver v w) (E : WeierstrassCurve k)
    (hstable : HasStableReductionAt E w) (h2 : v.maximalIdeal.valuation K 2 < 1)
    {n : ℕ} (hodd : Odd n) (hn : v.maximalIdeal.valuation K (n : K) = 1)
    (σ : K ≃ₐ[k] K) (hσ : σ ∈ v.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) (hσ2 : σ ^ 2 = 1)
    (Q : (Affine.baseChange E K).Point) (hQ : n • Q = 0) :
    Point.map (W' := E) (S := k) σ.toAlgHom Q = Q := by
  let ν := v.maximalIdeal.valuation K
  have hσ' (z : K) (hz : ν z ≤ 1) : ν (σ z - z) < 1 :=
    valuation_sub_lt_one_of_mem_inertia hσ hz
  have hσσ (z : K) : σ (σ z) = z := by
    have h := congrArg (fun τ : K ≃ₐ[k] K => τ z) hσ2
    rwa [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] at h
  obtain ⟨C, hC, hstable⟩ := exists_integralModel_of_hasStableReductionAt E w hstable
  let W := Affine.baseChange E K
  let C' := C.map (algebraMap k K)
  let W' := (C' • W).toAffine
  have hW' : W' = (C • E).map (algebraMap k K) :=
    map_variableChange E C (algebraMap k K)
  have hint : IsIntegralModel ν W' := by
    rw [hW']
    exact isIntegralModel_baseChange hvw hC
  have hcase : (ν W'.a₁ = 1 ∧ ν 2 < 1) ∨ ν W'.Δ = 1 := by
    rcases hstable with hΔ | hc₄
    · exact Or.inr (by rw [hW', map_Δ]; exact (valuation_map_eq_one_iff hvw _).2 hΔ)
    · have hc₄' : ν W'.c₄ = 1 := by
        rw [hW', map_c₄]
        exact (valuation_map_eq_one_iff hvw _).2 hc₄
      exact Or.inl ⟨InertiaInvolution.valuation_a₁_eq_one_of_c₄ ν hint hc₄' h2, h2⟩
  have hfix₁ : σ W'.a₁ = W'.a₁ := by rw [hW', map_a₁]; exact σ.commutes _
  have hfix₂ : σ W'.a₂ = W'.a₂ := by rw [hW', map_a₂]; exact σ.commutes _
  have hfix₃ : σ W'.a₃ = W'.a₃ := by rw [hW', map_a₃]; exact σ.commutes _
  have hfix₄ : σ W'.a₄ = W'.a₄ := by rw [hW', map_a₄]; exact σ.commutes _
  let φ := Point.map (W' := E) (S := k) σ.toAlgHom
  have hφ (a b : K) (h : W.Nonsingular a b) :
      ∃ h' : W.Nonsingular (σ a) (σ b), φ (.some a b h) = .some (σ a) (σ b) h' :=
    ⟨_, Point.map_some σ.toAlgHom h⟩
  let e := Anabelian.vcEquiv C' W
  let ψ := e.toAddMonoidHom.comp (φ.comp e.symm.toAddMonoidHom)
  have hfixU : σ (C'.u : K) = C'.u := by
    change σ (algebraMap k K (C.u : k)) = algebraMap k K (C.u : k)
    exact σ.commutes _
  have hψ (a b : K) (h : W'.Nonsingular a b) :
      ∃ h' : W'.Nonsingular (σ a) (σ b), ψ (.some a b h) = .some (σ a) (σ b) h' :=
    exists_vcEquiv_map_eq C' W (σ : K →+* K)
      hfixU (σ.commutes _) (σ.commutes _) (σ.commutes _) φ hφ a b h
  have hQ' : n • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
  have hfix := InertiaInvolution.map_eq_self ν hint (σ : K →+* K) hσσ hσ' hfix₁ hfix₂
    hfix₃ hfix₄ hcase hodd hn ψ hψ (e Q) hQ'
  change e (φ (e.symm (e Q))) = e Q at hfix
  rw [AddEquiv.symm_apply_apply] at hfix
  exact e.injective hfix

end BaseChange

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (R : (P.curve x).ModEllRepData ℓ)
  (v : FinitePlace ↥R.torsionField)

set_option quotPrecheck false in
local notation "K" => ↥R.torsionField
set_option quotPrecheck false in
local notation "F" => (P.curve x).F
set_option quotPrecheck false in
local notation "E" => (P.curve x).E

noncomputable local instance (priority := 1100) tameTwoDecidableEqTorsionField : DecidableEq K :=
  fun a b => Classical.propDecidable (a = b)

private theorem eq_one_of_sq_eq_one_of_mem_inertia
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (h2 : residueChar v = 2)
    (σ : K ≃ₐ[F] K) (hσ : σ ∈ v.maximalIdeal.asIdeal.inertia (K ≃ₐ[F] K)) (hσ2 : σ ^ 2 = 1) :
    σ = 1 := by
  let w := placeUnder (k := F) v
  have hvw : FinitePlace.LiesOver v w := liesOver_placeUnder v
  let ν := v.maximalIdeal.valuation K
  have hℓ' : ν (ℓ : K) = 1 :=
    (valuation_natCast_eq_one_iff v hℓ).2 (fun h => hℓ2 (h.symm.trans h2))
  have h2' : ν 2 < 1 := by
    refine lt_of_le_of_ne (valuation_natCast_le_one ν 2) fun h => ?_
    exact (valuation_natCast_eq_one_iff v Nat.prime_two).1 h h2
  refine R.eq_one_of_forall_torsion σ fun Q hQ => ?_
  exact torsion_fixed_by_inertia_involution hvw E ((P.arith x).stable_reduction w) h2'
    (hℓ.odd_of_ne_two hℓ2) hℓ' σ hσ hσ2 Q hQ

/-- The mod-ℓ torsion field is tamely ramified at a place of residue characteristic 2. -/
theorem not_two_dvd_relRamIdx_torsionField (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (h2 : residueChar v = 2) :
    ¬ 2 ∣ relRamIdx v (placeUnder (k := F) v) := by
  rw [relRamIdx_eq_card_inertia (liesOver_placeUnder (k := F) v)]
  intro hdvd
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτ2' : τ.1 ^ 2 = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hτ2
  have hτ1 : τ = 1 :=
    Subtype.ext (eq_one_of_sq_eq_one_of_mem_inertia P x R v hℓ hℓ2 h2 τ.1 τ.2 hτ2')
  rw [hτ1, orderOf_one] at hτ
  exact (by decide : (1 : ℕ) ≠ 2) hτ

end AbcAdaptation.Tripod
