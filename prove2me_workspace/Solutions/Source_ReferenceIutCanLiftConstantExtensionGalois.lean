/-
Source: Pi1/Orbicurve/BaseChange.lean at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftConstantExtension
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationGalois
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PrimitiveElement

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin Pointwise

universe u

noncomputable section

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω]
  [Algebra k Ω] [IsScalarTower k K Ω] {t : Ω}

attribute [local instance] fieldRingAction

section Closure

variable [IsAlgClosed Ω] [CharZero k]

lemma rootSet_map_rationalBaseMap (p : (rationalBase k t)[X]) :
    (p.map (rationalBaseMap (K := K) t)).rootSet Ω = p.rootSet Ω := by
  classical
  rw [Polynomial.rootSet_def, Polynomial.rootSet_def, Polynomial.aroots_def,
    Polynomial.aroots_def, Polynomial.map_map] <;> rfl

/-- **Galois closures and their base changes**: every finite extension `F` of `k(t)` in `Ω` lies in
a finite Galois extension `N` of `k(t)` whose compositum `N' = K(t) · N` is finite Galois over
`K(t)`. -/
theorem exists_galois_constantExtension (F : IntermediateField (rationalBase k t) Ω)
    [FiniteDimensional (rationalBase k t) F] :
    ∃ (N : IntermediateField (rationalBase k t) Ω) (N' : IntermediateField (rationalBase K t) Ω),
      F ≤ N ∧ FiniteDimensional (rationalBase k t) N ∧ IsGalois (rationalBase k t) N ∧
      FiniteDimensional (rationalBase K t) N' ∧ IsGalois (rationalBase K t) N' ∧ (∀ x ∈ N, x ∈ N') ∧
      N' = IntermediateField.adjoin (rationalBase K t) (N : Set Ω) := by
  classical
  haveI : CharZero (rationalBase k t) := charZero_of_injective_algebraMap (algebraMap k (rationalBase k t)).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : CharZero (rationalBase K t) := charZero_of_injective_algebraMap (algebraMap K (rationalBase K t)).injective
  letI : Algebra.IsSeparable (rationalBase k t) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (rationalBase k t) F
  set θ : Ω := (α : Ω)
  have hθint : IsIntegral (rationalBase k t) θ :=
    (IsIntegral.of_finite (rationalBase k t) α).map (IsScalarTower.toAlgHom (rationalBase k t) F Ω)
  set p := minpoly (rationalBase k t) θ
  have hp0 : p ≠ 0 := minpoly.ne_zero hθint
  set R := p.rootSet Ω
  set N := IntermediateField.adjoin (rationalBase k t) R
  set p' := p.map (rationalBaseMap (K := K) t)
  set N' := IntermediateField.adjoin (rationalBase K t) (p'.rootSet Ω)
  have hR : p'.rootSet Ω = R := rootSet_map_rationalBaseMap p
  haveI hsN : p.IsSplittingField (rationalBase k t) N :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI hsN' : p'.IsSplittingField (rationalBase K t) N' :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional (rationalBase k t) N := Polynomial.IsSplittingField.finiteDimensional N p
  haveI : FiniteDimensional (rationalBase K t) N' := Polynomial.IsSplittingField.finiteDimensional N' p'
  haveI : Normal (rationalBase k t) N := Normal.of_isSplittingField p
  haveI : Normal (rationalBase K t) N' := Normal.of_isSplittingField p'
  haveI : Algebra.IsSeparable (rationalBase k t) N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable (rationalBase K t) N' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hθR : θ ∈ R := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hp0, minpoly.aeval _ _⟩
  have hFN : F ≤ N := by
    intro x hx
    have h1 : (⟨x, hx⟩ : F) ∈ (rationalBase k t)⟮α⟯ := hα ▸ IntermediateField.mem_top
    have h2 : x ∈ ((rationalBase k t)⟮α⟯).map F.val := ⟨_, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    exact (IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.subset_adjoin _ _ hθR)) h2
  have hNN' : ∀ x ∈ N, x ∈ N' := by
    let N'k : IntermediateField (rationalBase k t) Ω :=
      N'.toSubfield.toIntermediateField fun c => N'.algebraMap_mem (rationalBaseMap (K := K) t c)
    have : N ≤ N'k := by
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      change y ∈ N'
      rw [← hR] at hy
      exact IntermediateField.subset_adjoin _ _ hy
    exact fun x hx => this hx
  refine ⟨N, N', hFN, inferInstance, IsGalois.mk, inferInstance, IsGalois.mk, hNN', ?_⟩
  apply le_antisymm
  · show IntermediateField.adjoin (rationalBase K t) (p'.rootSet Ω) ≤ _
    rw [hR]
    exact IntermediateField.adjoin.mono _ _ _ (IntermediateField.subset_adjoin _ _)
  · rw [IntermediateField.adjoin_le_iff]
    exact fun x hx => hNN' x hx

end Closure

/-- Evaluation of polynomials over `k(t)` at elements of an intermediate field over `K(t)`. -/
private lemma coe_aeval_constantExtensionMap (F' : IntermediateField (rationalBase K t) Ω) (q : (rationalBase k t)[X]) (z : F') :
    ((aeval z (q.map (rationalBaseMap (K := K) t)) : F') : Ω) = aeval (z : Ω) q := by
  have h1 : ((aeval z (q.map (rationalBaseMap (K := K) t)) : F') : Ω) =
      aeval (algebraMap F' Ω z) (q.map (rationalBaseMap (K := K) t)) :=
    (Polynomial.aeval_algebraMap_apply Ω z _).symm
  rw [h1, aeval_def, eval₂_map, aeval_def] <;> rfl

section Res

variable {N : IntermediateField (rationalBase k t) Ω} {N' : IntermediateField (rationalBase K t) Ω}
  (hN : ∀ x ∈ N, x ∈ N')

/-- Automorphisms of `N'` over `K(t)` preserve the normal extension `N` of `k(t)`. -/
private lemma mem_of_constantExtensionAut [Normal (rationalBase k t) N] (σ' : N' ≃ₐ[rationalBase K t] N') (x : N') (hx : (x : Ω) ∈ N) :
    ((σ' x : N') : Ω) ∈ N := by
  set q := minpoly (rationalBase k t) (x : Ω)
  have hint : IsIntegral (rationalBase k t) (x : Ω) := by
    have := Normal.isIntegral (F := rationalBase k t) (K := N) inferInstance ⟨x, hx⟩
    exact this.map (IsScalarTower.toAlgHom (rationalBase k t) N Ω)
  have hq0 : q ≠ 0 := minpoly.ne_zero hint
  have hq : aeval (x : Ω) q = 0 := minpoly.aeval _ _
  have h1 : aeval x (q.map (rationalBaseMap (K := K) t)) = 0 := by
    apply Subtype.ext
    rw [coe_aeval_constantExtensionMap, hq]; rfl
  have h2 : aeval (σ' x) (q.map (rationalBaseMap (K := K) t)) = 0 := by
    rw [Polynomial.aeval_algHom_apply σ', h1, map_zero]
  have h3 : aeval ((σ' x : N') : Ω) q = 0 := by
    rw [← coe_aeval_constantExtensionMap, h2]; rfl
  have hsplit : (q.map (algebraMap (rationalBase k t) N)).Splits := by
    have := Normal.splits (F := rationalBase k t) (K := N) inferInstance ⟨x, hx⟩
    rwa [IntermediateField.minpoly_eq] at this
  have hroot : ((q.map (algebraMap (rationalBase k t) N)).map (algebraMap N Ω)).IsRoot ((σ' x : N') : Ω) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.IsRoot, eval_map,
      ← aeval_def]
    exact h3
  obtain ⟨y, hy⟩ := hsplit.mem_range_of_isRoot (Polynomial.map_ne_zero hq0) hroot
  rw [← hy]
  exact y.2

variable [Normal (rationalBase k t) N]

/-- The restriction of an automorphism of `N'` to `N`, as a function. -/
private def constantExtensionResFun (σ' : N' ≃ₐ[rationalBase K t] N') (x : N) : N :=
  ⟨σ' ⟨x, hN x x.2⟩, mem_of_constantExtensionAut σ' _ x.2⟩

private lemma coe_constantExtensionResFun (σ' : N' ≃ₐ[rationalBase K t] N') (x : N) :
    ((constantExtensionResFun hN σ' x : N) : Ω) = ((σ' ⟨x, hN x x.2⟩ : N') : Ω) := rfl

/-- **Restriction** `Gal(N' / K(t)) → Gal(N / k(t))`. -/
def constantExtensionRes : (N' ≃ₐ[rationalBase K t] N') →* (N ≃ₐ[rationalBase k t] N) where
  toFun σ' :=
    { toFun := constantExtensionResFun hN σ'
      invFun := constantExtensionResFun hN σ'.symm
      left_inv x := Subtype.ext (by
        simp only [coe_constantExtensionResFun]
        have : (⟨((σ' ⟨x, hN x x.2⟩ : N') : Ω), hN _ (mem_of_constantExtensionAut σ' _ x.2)⟩ : N') =
            σ' ⟨x, hN x x.2⟩ := rfl
        rw [this, AlgEquiv.symm_apply_apply])
      right_inv x := Subtype.ext (by
        simp only [coe_constantExtensionResFun]
        have : (⟨((σ'.symm ⟨x, hN x x.2⟩ : N') : Ω), hN _ (mem_of_constantExtensionAut σ'.symm _ x.2)⟩ : N') =
            σ'.symm ⟨x, hN x x.2⟩ := rfl
        rw [this, AlgEquiv.apply_symm_apply])
      map_mul' x y := Subtype.ext (by
        change ((σ' (⟨x, hN x x.2⟩ * ⟨y, hN y y.2⟩) : N') : Ω) = _
        rw [map_mul]; rfl)
      map_add' x y := Subtype.ext (by
        change ((σ' (⟨x, hN x x.2⟩ + ⟨y, hN y y.2⟩) : N') : Ω) = _
        rw [map_add]; rfl)
      commutes' c := Subtype.ext (by
        simp only [coe_constantExtensionResFun]
        have : (⟨((algebraMap (rationalBase k t) N c : N) : Ω), hN _ (algebraMap (rationalBase k t) N c).2⟩ : N') =
            algebraMap (rationalBase K t) N' (rationalBaseMap t c) := rfl
        rw [this, AlgEquiv.commutes]; rfl) }
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp] lemma coe_constantExtensionRes_apply (σ' : N' ≃ₐ[rationalBase K t] N') (x : N) :
    ((constantExtensionRes hN σ' x : N) : Ω) = ((σ' ⟨x, hN x x.2⟩ : N') : Ω) := rfl

end Res

/-- Membership in the lower base field implies membership in the upper base field. -/
theorem bot_mem_constantExtension : ∀ x ∈ (⊥ : IntermediateField (rationalBase k t) Ω),
    x ∈ (⊥ : IntermediateField (rationalBase K t) Ω) := by
  intro x hx
  obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact IntermediateField.mem_bot.mpr ⟨rationalBaseMap t c, rfl⟩

private theorem constantExtensionAut_fixes_adjoin
    {N' : IntermediateField (rationalBase K t) Ω}
    (σ' : N' ≃ₐ[rationalBase K t] N') {S : Set Ω} (hS : ∀ x ∈ S, x ∈ N')
    (h : ∀ x : N', (x : Ω) ∈ S → σ' x = x) (x : N')
    (hx : (x : Ω) ∈ IntermediateField.adjoin (rationalBase K t) S) : σ' x = x := by
  have hle : IntermediateField.adjoin (rationalBase K t) S ≤ N' :=
    IntermediateField.adjoin_le_iff.mpr hS
  let ι := IntermediateField.inclusion hle
  have heq : σ'.toAlgHom.comp ι = ι := by
    apply IntermediateField.adjoin_algHom_ext
    exact fun a ha => h ⟨a, hS a ha⟩ ha
  exact DFunLike.congr_fun heq ⟨x, hx⟩

section Restriction

variable {N : IntermediateField (rationalBase k t) Ω} {N' : IntermediateField (rationalBase K t) Ω}
  (hN : ∀ x ∈ N, x ∈ N') [Normal (rationalBase k t) N]

theorem constantExtensionRes_injective
    (hN' : N' ≤ IntermediateField.adjoin (rationalBase K t) (N : Set Ω)) :
    Function.Injective (constantExtensionRes hN) := by
  rw [injective_iff_map_eq_one]
  intro σ' hσ'
  ext x
  have h (y : N') (hy : (y : Ω) ∈ N) : σ' y = y := by
    have heq := AlgEquiv.congr_fun hσ' (⟨y, hy⟩ : N)
    have hf := congrArg (fun z : N => (z : Ω)) heq
    rw [coe_constantExtensionRes_apply] at hf
    exact Subtype.ext hf
  exact congrArg Subtype.val (constantExtensionAut_fixes_adjoin σ' hN h x (hN' x.2))

theorem constantExtensionRes_mem_fixSub {F : IntermediateField (rationalBase k t) Ω}
    {F' : IntermediateField (rationalBase K t) Ω} (hFN : F ≤ N) (hF : ∀ x ∈ F, x ∈ F')
    (hF' : F' ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω))
    (σ' : N' ≃ₐ[rationalBase K t] N') :
    σ' ∈ fixSub N' F' ↔ constantExtensionRes hN σ' ∈ fixSub N F := by
  constructor
  · intro h x hx
    apply Subtype.ext
    rw [coe_constantExtensionRes_apply]
    exact congrArg Subtype.val (h ⟨x, hN x x.2⟩ (hF _ hx))
  · intro h x hx
    refine constantExtensionAut_fixes_adjoin σ' (fun y hy => hN y (hFN hy)) (fun y hy => ?_) x
      (hF' hx)
    have heq := congrArg Subtype.val (h ⟨y, hFN hy⟩ hy)
    rw [coe_constantExtensionRes_apply] at heq
    exact Subtype.ext heq

theorem constantExtensionMap_smul (σ' : N' ≃ₐ[rationalBase K t] N')
    (x : coordRing t N) : constantExtensionMap hN (constantExtensionRes hN σ' • x) =
      σ' • constantExtensionMap hN x := by
  apply Subtype.ext
  apply Subtype.ext
  change ((constantExtensionRes hN σ' (x : N) : N) : Ω) =
    ((σ' ⟨x, hN _ (x : N).2⟩ : N') : Ω)
  exact coe_constantExtensionRes_apply hN σ' x

theorem constantExtensionRes_mem_inertia (P' : Ideal (coordRing t N'))
    (σ' : N' ≃ₐ[rationalBase K t] N') (hσ : σ' ∈ P'.inertia (N' ≃ₐ[rationalBase K t] N')) :
    constantExtensionRes hN σ' ∈ (P'.comap (constantExtensionMap hN)).inertia
      (N ≃ₐ[rationalBase k t] N) := by
  intro x
  change constantExtensionMap hN (constantExtensionRes hN σ' • x - x) ∈ P'
  rw [map_sub, constantExtensionMap_smul]
  exact hσ _

end Restriction

/-- **Restriction is surjective** when `k` is algebraically closed (`K(t) ∩ N = k(t)`). -/
theorem constantExtensionRes_surjective [IsAlgClosed k] (htK : Transcendental K t)
    {N : IntermediateField (rationalBase k t) Ω} {N' : IntermediateField (rationalBase K t) Ω}
    (hN : ∀ x ∈ N, x ∈ N') [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N]
    [FiniteDimensional (rationalBase K t) N'] [IsGalois (rationalBase K t) N'] :
    Function.Surjective (constantExtensionRes hN) := by
  rw [← MonoidHom.range_eq_top]
  set H := (constantExtensionRes hN).range
  have hfix : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    -- `x` is fixed by `Gal(N' / K(t))`, so `x ∈ K(t)`
    have hx' : (⟨x, hN x x.2⟩ : N') ∈ (⊥ : IntermediateField (rationalBase K t) N') := by
      rw [← IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField (rationalBase K t) N'),
        IntermediateField.fixingSubgroup_bot, IntermediateField.mem_fixedField_iff]
      intro σ' _
      have := congrArg Subtype.val (hx (constantExtensionRes hN σ') ⟨σ', rfl⟩)
      rw [coe_constantExtensionRes_apply] at this
      exact Subtype.ext this
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hx'
    have hxK : (x : Ω) ∈ rationalBase K t := by
      rw [← congrArg Subtype.val hc]; exact c.2
    have halg : IsAlgebraic (rationalBase k t) (x : Ω) :=
      ((IsIntegral.of_finite (rationalBase k t) x).map (IsScalarTower.toAlgHom (rationalBase k t) N Ω)).isAlgebraic
    have hxk := mem_rationalBase_of_isAlgebraic_extension htK hxK halg
    exact IntermediateField.mem_bot.mpr ⟨⟨x, hxk⟩, Subtype.ext rfl⟩
  rw [← IntermediateField.fixingSubgroup_fixedField H, hfix, IntermediateField.fixingSubgroup_bot]

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
