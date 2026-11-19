/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/U2/Realize.lean and OrbicurveCores/U2/CoreMap.lean
-/
import Solutions.Source_ReferenceIutCanLiftNoether
import Solutions.Source_ReferenceIutCanLiftNormalizationEmbed
import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentation
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option autoImplicit false

/-!
# Realizing a finite étale cover of affine orbicurves inside a fixed field

A Noether normalization parameter of the target identifies both coordinate rings with
normalizations in an algebraic closure of the rational function field. The cover is the
inclusion of the two normalization rings.
-/

open Polynomial IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AbcAdaptation.Reference.Iut.Anabelian

open JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation (Cover)
open JoshiTeich.Act1Scene1.FunctionFieldNormalization

universe u

/-- The ambient field: an algebraic closure of `k(t)`. -/
abbrev ratFuncClosure (k : Type u) [Field k] : Type u := AlgebraicClosure (RatFunc k)

/-- The transcendental `t ∈ Ω`. -/
noncomputable def ratFuncClosureParameter (k : Type u) [Field k] : ratFuncClosure k :=
  algebraMap (RatFunc k) (ratFuncClosure k) RatFunc.X

variable {k : Type u} [Field k]

local notation "Ω" => ratFuncClosure k
local notation "t" => ratFuncClosureParameter k
local notation "K₀" => rationalBase k t
local notation "T" => (⊥ : IntermediateField K₀ Ω)

theorem transcendental_ratFuncClosureParameter : Transcendental k (ratFuncClosureParameter k) := by
  have h := RatFunc.transcendental_X (K := k)
  unfold ratFuncClosureParameter
  intro halg
  apply h
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom k (RatFunc k) Ω)
    (algebraMap (RatFunc k) Ω).injective).mp halg

/-- `k[t] → coordRing ⊥` is bijective. -/
theorem bijective_algebraMap_bot :
    Function.Bijective
      (algebraMap (polynomialBase k t) (coordRing t T)) := by
  refine ⟨fun a b h ↦ Subtype.ext (congrArg (fun c : coordRing t T ↦ ((c : T) : Ω)) h),
    fun b ↦ ?_⟩
  have hb : ((b : T) : Ω) ∈ T := (b : T).2
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hb
  haveI := principalBase t transcendental_ratFuncClosureParameter
  have hzint : IsIntegral (polynomialBase k t) z := by
    have h1 := isIntegral_of_mem_coordRing t b
    rw [← hz] at h1
    haveI : IsScalarTower (polynomialBase k t) K₀ Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact (isIntegral_algebraMap_iff (algebraMap K₀ Ω).injective).mp h1
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := polynomialBase k t) (K := K₀)).mp hzint
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  rw [← hz, ← ha]
  rfl

/-- `k[t] ≅ coordRing ⊥`. -/
noncomputable def eBot : polynomialBase k t ≃ₐ[k] coordRing t T :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom k (polynomialBase k t) _) bijective_algebraMap_bot

private noncomputable def polynomialEquivBot : k[X] ≃ₐ[k] coordRing t T :=
  (Polynomial.algEquivOfTranscendental k t
    (transcendental_ratFuncClosureParameter (k := k))).trans (eBot (k := k))

/-- The map `coordRing ⊥ = k[t] → A`, `t ↦ c₀`. -/
noncomputable def gBase {A : Type u} [CommRing A] [Algebra k A] (c₀ : A) :
    coordRing t T →ₐ[k] A :=
  (aeval c₀ : k[X] →ₐ[k] A).comp (polynomialEquivBot (k := k)).symm.toAlgHom

theorem gBase_injective {A : Type u} [CommRing A] [Algebra k A] {c₀ : A}
    (hc : Transcendental k c₀) : Function.Injective (gBase (k := k) c₀) := by
  have heval : Function.Injective (aeval c₀ : k[X] →ₐ[k] A) :=
    transcendental_iff_injective.mp hc
  exact heval.comp (polynomialEquivBot (k := k)).symm.injective

theorem gBase_range {A : Type u} [CommRing A] [Algebra k A] (c₀ : A) (a : A)
    (ha : a ∈ Algebra.adjoin k {c₀}) : ∃ b : coordRing t T, gBase (k := k) c₀ b = a := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨p, hp⟩ := (AlgHom.mem_range (aeval c₀ : k[X] →ₐ[k] A)).mp ha
  refine ⟨polynomialEquivBot (k := k) p, ?_⟩
  simpa only [gBase, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] using hp

private noncomputable def gBaseToAdjoin {A : Type u} [CommRing A] [Algebra k A] (c₀ : A) :
    coordRing t T →+* Algebra.adjoin k ({c₀} : Set A) :=
  (gBase (k := k) c₀).toRingHom.codRestrict (Algebra.adjoin k ({c₀} : Set A)) (by
    intro b
    change (aeval c₀ : k[X] →ₐ[k] A) ((polynomialEquivBot (k := k)).symm b) ∈
      Algebra.adjoin k {c₀}
    exact Polynomial.aeval_mem_adjoin_singleton k c₀)

theorem gBase_isIntegral {A : Type u} [CommRing A] [Nontrivial A] [Algebra k A] {c₀ : A}
    (hint : ∀ a : A, IsIntegral (Algebra.adjoin k {c₀}) a) :
    (gBase (k := k) c₀).toRingHom.IsIntegral := by
  let S : Subalgebra k A := Algebra.adjoin k {c₀}
  let f : coordRing t T →+* S := gBaseToAdjoin (k := k) c₀
  let ι : S →+* A := algebraMap S A
  have hsurj : Function.Surjective f := by
    intro s
    obtain ⟨b, hb⟩ := gBase_range (k := k) c₀ (s : A) s.property
    refine ⟨b, Subtype.ext ?_⟩
    change gBase (k := k) c₀ b = (s : A)
    exact hb
  have hint' : ι.IsIntegral := hint
  have hcomp : (gBase (k := k) c₀).toRingHom = ι.comp f :=
    RingHom.ext fun _ => rfl
  rw [hcomp]
  exact RingHom.IsIntegral.trans f ι (RingHom.isIntegral_of_surjective f hsurj) hint'

/-- **Realization** of a finite étale morphism `Z → C` inside `Ω`. -/
theorem exists_realization {C Z : AffineOrbicurvePresentation k} (φ : Cover Z C) :
    ∃ (F L : IntermediateField K₀ Ω) (_ : FiniteDimensional K₀ F)
      (_ : FiniteDimensional K₀ L) (hFL : F ≤ L)
      (ψC : C.A ≃ₐ[k] coordRing t F) (ψZ : Z.A ≃ₐ[k] coordRing t L),
      ∀ a, ψZ (φ.f a) = ringMap hFL (ψC a) := by
  obtain ⟨c₀, hc₀, hint⟩ := exists_transcendental_isIntegral (k := k) (A := C.A) C.not_isField
  let g₁ : coordRing t T →ₐ[k] C.A := gBase (k := k) c₀
  have hg₁ : Function.Injective g₁ := gBase_injective (k := k) (c₀ := c₀) hc₀
  have hg₁i : g₁.toRingHom.IsIntegral := gBase_isIntegral (k := k) (c₀ := c₀) hint
  obtain ⟨F, hFfin, -, ψC, -⟩ :=
    exists_algEquiv_coordRing (k := k) t (B := T) C.A g₁ hg₁ hg₁i
  letI : FiniteDimensional (rationalBase k t) F := hFfin
  let g₂ : coordRing t F →ₐ[k] Z.A := φ.f.comp ψC.symm.toAlgHom
  have hg₂ : Function.Injective g₂ := φ.injective.comp ψC.symm.injective
  have hg₂i : g₂.toRingHom.IsIntegral := by
    let f : coordRing t F →+* C.A := ψC.symm.toRingEquiv.toRingHom
    have hf : f.IsIntegral := RingHom.isIntegral_of_surjective f ψC.symm.surjective
    have hcomp : g₂.toRingHom = φ.f.toRingHom.comp f := RingHom.ext fun _ => rfl
    rw [hcomp]
    exact RingHom.IsIntegral.trans f φ.f.toRingHom hf φ.isIntegral
  obtain ⟨L, hLfin, hFL, ψZ, hψZ⟩ :=
    exists_algEquiv_coordRing (k := k) t (B := F) Z.A g₂ hg₂ hg₂i
  refine ⟨F, L, hFfin, hLfin, hFL, ψC, ψZ, fun a ↦ ?_⟩
  have := hψZ (ψC a)
  simp only [g₂, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] at this
  exact this

/-- `k(t) ⊆ K₀`. -/
theorem algebraMap_ratFunc_mem (f : RatFunc k) : algebraMap (RatFunc k) Ω f ∈ K₀ := by
  have hp : ∀ p : Polynomial k, algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k) p)
      ∈ K₀ := fun p ↦ by
    have e : algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k) p) =
        Polynomial.aeval t p := by
      rw [← RatFunc.aeval_X_left_eq_algebraMap, ratFuncClosureParameter]
      exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k (RatFunc k) Ω)
        RatFunc.X p).symm
    rw [e]
    exact IntermediateField.algebra_adjoin_le_adjoin k _
      (Polynomial.aeval_mem_adjoin_singleton k t)
  rw [← RatFunc.num_div_denom f, map_div₀]
  exact div_mem (hp _) (hp _)

/-- `Ω` is normal over `K₀`. -/
instance normal_ratFuncClosure : Normal K₀ Ω := by
  haveI : Algebra.IsAlgebraic K₀ Ω := ⟨fun x ↦ by
    have hx : IsAlgebraic (RatFunc k) x := Algebra.IsAlgebraic.isAlgebraic x
    obtain ⟨p, hp0, hp⟩ := hx
    let ρ : RatFunc k →+* K₀ :=
      (algebraMap (RatFunc k) Ω).codRestrict (rationalBase k t)
        (algebraMap_ratFunc_mem (k := k))
    have hρ : (algebraMap K₀ Ω).comp ρ = algebraMap (RatFunc k) Ω :=
      RingHom.ext fun _ => rfl
    refine ⟨p.map ρ, (Polynomial.map_ne_zero_iff ρ.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hρ]
    exact hp⟩
  exact { splits' := fun x ↦ IsAlgClosed.splits _ }

/-- The original complex instance of the ambient field. -/
abbrev Ωt : Type := ratFuncClosure ℂ

noncomputable def tΩ : Ωt := ratFuncClosureParameter ℂ

theorem transcendental_tΩ : Transcendental ℂ tΩ := transcendental_ratFuncClosureParameter

theorem normal_Ωt : Normal (rationalBase ℂ tΩ) Ωt := normal_ratFuncClosure

end AbcAdaptation.Reference.Iut.Anabelian
