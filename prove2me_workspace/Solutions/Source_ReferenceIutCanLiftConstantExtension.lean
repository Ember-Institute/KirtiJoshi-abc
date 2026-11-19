/-
Source: Pi1/Orbicurve/BaseChange.lean (constant inclusions and relative algebraic closure)
and Pi1/Orbicurve/Descent.lean (polynomial intersection and integrality descent)
at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.

The proof uses Mathlib's integrality lemmas for coefficients and minimal polynomials.
-/
import Solutions.Source_ReferenceIutCanLiftNormalizationEmbed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.IsIntegral

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Polynomial IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω]
  [Algebra k Ω] [IsScalarTower k K Ω] {t : Ω}

theorem mem_rationalBase_extension {x : Ω} (hx : x ∈ rationalBase k t) :
    x ∈ rationalBase K t := by
  have h : rationalBase k t ≤ (rationalBase K t).restrictScalars k :=
    IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self K t))
  exact h hx

theorem mem_polynomialBase_extension {x : Ω} (hx : x ∈ polynomialBase k t) :
    x ∈ polynomialBase K t := by
  have h : polynomialBase k t ≤ (polynomialBase K t).restrictScalars k :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Algebra.self_mem_adjoin_singleton K t))
  exact h hx

/-- The inclusion of polynomial rings induced by extension of constants. -/
def polynomialBaseMap (t : Ω) : polynomialBase k t →+* polynomialBase K t :=
  (polynomialBase k t).val.toRingHom.codRestrict (polynomialBase K t)
    (fun a => mem_polynomialBase_extension a.2)

/-- The inclusion of rational function fields induced by extension of constants. -/
def rationalBaseMap (t : Ω) : rationalBase k t →+* rationalBase K t where
  toFun a := ⟨a, mem_rationalBase_extension a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem transcendental_of_constantExtension (ht : Transcendental K t) : Transcendental k t :=
  fun h => ht (h.extendScalars (algebraMap k K).injective)

theorem isIntegral_polynomialBase_extension {x : Ω} (hx : IsIntegral (polynomialBase k t) x) :
    IsIntegral (polynomialBase K t) x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (polynomialBaseMap t), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx

/-- Inclusion of normalization rings for ambient subfields related by extension of constants. -/
def constantExtensionMap {F : IntermediateField (rationalBase k t) Ω}
    {F' : IntermediateField (rationalBase K t) Ω} (h : ∀ x ∈ F, x ∈ F') :
    coordRing t F →+* coordRing t F' where
  toFun a := ⟨⟨(a : F), h _ (a : F).2⟩,
    mem_coordRing_of_isIntegral t (h _ (a : F).2)
      (isIntegral_polynomialBase_extension (isIntegral_of_mem_coordRing t a))⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coe_constantExtensionMap {F : IntermediateField (rationalBase k t) Ω}
    {F' : IntermediateField (rationalBase K t) Ω} (h : ∀ x ∈ F, x ∈ F') (a : coordRing t F) :
    ((constantExtensionMap h a : F') : Ω) = ((a : F) : Ω) := rfl

theorem constantExtensionMap_injective {F : IntermediateField (rationalBase k t) Ω}
    {F' : IntermediateField (rationalBase K t) Ω} (h : ∀ x ∈ F, x ∈ F') :
    Function.Injective (constantExtensionMap h) := fun _ _ hab =>
  Subtype.ext (Subtype.ext (congrArg (fun c : coordRing t F' => ((c : F') : Ω)) hab))

theorem constantExtensionMap_comp_ringMap {F L : IntermediateField (rationalBase k t) Ω}
    {F' L' : IntermediateField (rationalBase K t) Ω} (hF : ∀ x ∈ F, x ∈ F')
    (hL : ∀ x ∈ L, x ∈ L') (h : F ≤ L) (h' : F' ≤ L') :
    (ringMap h').toRingHom.comp (constantExtensionMap hF) =
      (constantExtensionMap hL).comp (ringMap h).toRingHom :=
  RingHom.ext fun _ => rfl

/-- Inside the ambient field, the intersection of K[t] and k(t) is k[t]. -/
theorem mem_polynomialBase_of_mem_extension (ht : Transcendental K t) {z : Ω}
    (hz : z ∈ rationalBase k t) (hzK : z ∈ polynomialBase K t) : z ∈ polynomialBase k t := by
  classical
  obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff k z).mp hz
  have hR : ∃ R : K[X], aeval t R = z := by
    change z ∈ (aeval t : K[X] →ₐ[K] Ω).range
    rwa [← Algebra.adjoin_singleton_eq_range_aeval]
  obtain ⟨R, hR⟩ := hR
  by_cases hQ : aeval t Q = 0
  · rw [hQ, div_zero] at hPQ
    rw [hPQ]
    exact zero_mem _
  have hQ0 : Q ≠ 0 := fun h => hQ (by rw [h, map_zero])
  have hrel : Q.map (algebraMap k K) * R = P.map (algebraMap k K) := by
    apply (transcendental_iff_injective.mp ht)
    rw [map_mul, aeval_map_algebraMap, aeval_map_algebraMap, hR, mul_comm]
    exact (eq_div_iff hQ).mp hPQ
  let D := P / Q
  let M := P % Q
  have hPM : P = Q * D + M := (EuclideanDomain.div_add_mod P Q).symm
  have hM : M.degree < Q.degree := EuclideanDomain.mod_lt P hQ0
  have hdiv : Q.map (algebraMap k K) * (R - D.map (algebraMap k K)) =
      M.map (algebraMap k K) := by
    rw [mul_sub, hrel, hPM, Polynomial.map_add, Polynomial.map_mul]
    exact add_sub_cancel_left _ _
  have hRD : R = D.map (algebraMap k K) := by
    by_contra hne
    have hne' := sub_ne_zero.mpr hne
    have hdeg := congrArg Polynomial.degree hdiv
    rw [Polynomial.degree_mul, Polynomial.degree_map, Polynomial.degree_map] at hdeg
    have h0 : (0 : WithBot ℕ) ≤ (R - D.map (algebraMap k K)).degree := by
      rw [Polynomial.degree_eq_natDegree hne']
      exact WithBot.coe_le_coe.mpr (Nat.zero_le _)
    have hle : Q.degree ≤ Q.degree + (R - D.map (algebraMap k K)).degree :=
      le_add_of_nonneg_right h0
    exact (not_le.mpr hM) (hdeg ▸ hle)
  rw [← hR, hRD, aeval_map_algebraMap]
  exact Polynomial.aeval_mem_adjoin_singleton k t

theorem mem_polynomialBase_of_isIntegral (ht : Transcendental K t) {z : Ω}
    (hz : z ∈ rationalBase K t) (hi : IsIntegral (polynomialBase K t) z) :
    z ∈ polynomialBase K t := by
  letI := principalBase t ht
  have hx : IsIntegral (polynomialBase K t) (⟨z, hz⟩ : rationalBase K t) :=
    (isIntegral_algebraMap_iff (algebraMap (rationalBase K t) Ω).injective).mp hi
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx
  have haz : (a : Ω) = z := congrArg (fun b : rationalBase K t => (b : Ω)) ha
  exact haz ▸ a.2

private theorem integral_constant_mem_range [IsAlgClosed k] {x : K} (hx : IsIntegral k x) :
    x ∈ Set.range (algebraMap k K) := by
  let F := IntermediateField.adjoin k {x}
  haveI : FiniteDimensional k F := IntermediateField.adjoin.finiteDimensional hx
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := F)).2
    ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩
  exact ⟨a, congrArg Subtype.val ha⟩

attribute [local instance] Polynomial.algebra in
private theorem mem_polynomialBase_of_isIntegral_extension [IsAlgClosed k]
    (ht : Transcendental K t) {z : Ω} (hz : z ∈ polynomialBase K t)
    (hi : IsIntegral (polynomialBase k t) z) : z ∈ polynomialBase k t := by
  let e := Polynomial.algEquivOfTranscendental k t (transcendental_of_constantExtension ht)
  have hcoe (P : k[X]) : ((e P : polynomialBase k t) : Ω) = aeval t P := by
    change ((aeval (⟨t, Algebra.self_mem_adjoin_singleton k t⟩ : polynomialBase k t) P :
      polynomialBase k t) : Ω) = _
    rw [← Subalgebra.aeval_coe]
  have hP : ∃ P : K[X], aeval t P = z := by
    change z ∈ (aeval t : K[X] →ₐ[K] Ω).range
    rwa [← Algebra.adjoin_singleton_eq_range_aeval]
  obtain ⟨P, hP⟩ := hP
  obtain ⟨f, hfm, hf⟩ := hi
  have hPint : IsIntegral k[X] P := by
    refine ⟨f.map e.symm.toRingEquiv.toRingHom, hfm.map _, ?_⟩
    apply (transcendental_iff_injective.mp ht)
    change (aeval t : K[X] →ₐ[K] Ω).toRingHom _ = _
    rw [map_zero, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    have hcomp : (aeval t : K[X] →ₐ[K] Ω).toRingHom.comp
        ((algebraMap k[X] K[X]).comp e.symm.toRingEquiv.toRingHom) =
          algebraMap (polynomialBase k t) Ω := by
      ext a
      obtain ⟨q, rfl⟩ := e.surjective a
      change aeval t ((e.symm (e q)).map (algebraMap k K)) = ((e q : polynomialBase k t) : Ω)
      rw [AlgEquiv.symm_apply_apply, Polynomial.aeval_map_algebraMap, hcoe]
    rw [hcomp]
    change f.eval₂ (algebraMap (polynomialBase k t) Ω) (aeval t P) = 0
    rw [hP]
    exact hf
  have hcoeff := (Polynomial.isIntegral_iff_isIntegral_coeff.mp hPint)
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts P).mp
    ((Polynomial.lifts_iff_coeff_lifts P).mpr (fun n => integral_constant_mem_range (hcoeff n)) :
      P ∈ Polynomial.lifts (algebraMap k K))
  rw [← hP, ← hQ, aeval_map_algebraMap]
  exact Polynomial.aeval_mem_adjoin_singleton k t

/-- The relative algebraic closure of k(t) in K(t) equals k(t) for algebraically closed k. -/
theorem mem_rationalBase_of_isAlgebraic_extension [IsAlgClosed k] (ht : Transcendental K t)
    {x : Ω} (hx : x ∈ rationalBase K t) (ha : IsAlgebraic (rationalBase k t) x) :
    x ∈ rationalBase k t := by
  have ha' : IsAlgebraic (polynomialBase k t) x :=
    (IsFractionRing.isAlgebraic_iff (polynomialBase k t) (rationalBase k t) Ω).mpr ha
  obtain ⟨b, hb, hbint⟩ := ha'.exists_integral_multiple
  have hbmem : (b : Ω) ∈ rationalBase k t :=
    IntermediateField.algebra_adjoin_le_adjoin k {t} b.2
  have hb0 : (b : Ω) ≠ 0 := fun h => hb (Subtype.ext h)
  have hmul : IsIntegral (polynomialBase k t) ((b : Ω) * x) := hbint
  have hmulK : (b : Ω) * x ∈ rationalBase K t :=
    mul_mem (mem_rationalBase_extension hbmem) hx
  have hpoly := mem_polynomialBase_of_isIntegral ht hmulK
    (isIntegral_polynomialBase_extension hmul)
  have hlow := mem_polynomialBase_of_isIntegral_extension ht hpoly hmul
  have heq : (b : Ω) * x / b = x := by field_simp
  rw [← heq]
  exact div_mem (IntermediateField.algebra_adjoin_le_adjoin k {t} hlow) hbmem

/-- Minimal polynomials of elements algebraic over k(t) survive extension of constants. -/
theorem map_minpoly_constantExtension [IsAlgClosed k] (ht : Transcendental K t) {x : Ω}
    (hx : IsIntegral (rationalBase k t) x) :
    (minpoly (rationalBase k t) x).map (rationalBaseMap t) = minpoly (rationalBase K t) x := by
  letI : Algebra (rationalBase k t) (rationalBase K t) := (rationalBaseMap t).toAlgebra
  letI : IsScalarTower (rationalBase k t) (rationalBase K t) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply minpoly.map_algebraMap hx
  apply (Polynomial.lifts_iff_coeff_lifts _).mpr
  intro n
  let p := minpoly (rationalBase k t) x
  let q := minpoly (rationalBase K t) x
  have hdiv : q ∣ p.map (algebraMap (rationalBase k t) (rationalBase K t)) :=
    minpoly.dvd_map_of_isScalarTower _ _ x
  have hi := Polynomial.isIntegral_coeff_of_dvd p q (minpoly.monic hx)
    (minpoly.monic hx.tower_top) hdiv n
  have hq : IsIntegral (rationalBase k t) ((q.coeff n : rationalBase K t) : Ω) :=
    hi.map (IsScalarTower.toAlgHom (rationalBase k t) (rationalBase K t) Ω)
  have hmem := mem_rationalBase_of_isAlgebraic_extension ht (q.coeff n).2 hq.isAlgebraic
  exact ⟨⟨q.coeff n, hmem⟩, Subtype.ext rfl⟩

/-- An element algebraic over k(t) and integral over K[t] is integral over k[t]. -/
theorem isIntegral_polynomialBase_of_constantExtension [IsAlgClosed k]
    (ht : Transcendental K t) {x : Ω} (hx : IsIntegral (rationalBase k t) x)
    (hi : IsIntegral (polynomialBase K t) x) : IsIntegral (polynomialBase k t) x := by
  letI := principalBase t ht
  let p := minpoly (rationalBase k t) x
  have hmap : p.map (rationalBaseMap t) =
      (minpoly (polynomialBase K t) x).map (algebraMap (polynomialBase K t) (rationalBase K t)) :=
    (map_minpoly_constantExtension ht hx).trans
      (minpoly.isIntegrallyClosed_eq_field_fractions' (rationalBase K t) hi)
  have hp : p ∈ Polynomial.lifts (algebraMap (polynomialBase k t) (rationalBase k t)) := by
    apply (Polynomial.lifts_iff_coeff_lifts p).mpr
    intro n
    have hcoeff := congrArg (fun q : (rationalBase K t)[X] => (q.coeff n : Ω)) hmap
    simp only [Polynomial.coeff_map] at hcoeff
    have hmem : (p.coeff n : Ω) ∈ polynomialBase K t := by
      rw [show (p.coeff n : Ω) = ((minpoly (polynomialBase K t) x).coeff n : Ω) from hcoeff]
      exact ((minpoly (polynomialBase K t) x).coeff n).2
    exact ⟨⟨p.coeff n, mem_polynomialBase_of_mem_extension ht (p.coeff n).2 hmem⟩,
      Subtype.ext rfl⟩
  obtain ⟨q, hq, _, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hp (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  change aeval x q = 0
  rw [← Polynomial.aeval_map_algebraMap (rationalBase k t), hq]
  exact minpoly.aeval _ _

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
