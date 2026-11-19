/-
Source: Pi1/Orbicurve/LefschetzMain.lean at revision
ca7def953193f861a462aa0831eec8f0a31ff69f, lines 66–83 and 129–241.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.

The lower field and the upper field lie in the same ambient field. The lower field contains
the chosen coordinates and generates the upper field after extension of constants.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalization
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.SetTheory.Cardinal.Subfield

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Cardinal Polynomial WeierstrassCurve
open JoshiTeich.Act1Scene1.FunctionFieldNormalization (rationalBase)
open scoped Polynomial

universe u

private theorem exists_countable_algClosed_subfield {K : Type u} [Field K] [IsAlgClosed K]
    (S : Set K) (hS : S.Finite) : ∃ k : Subfield K, IsAlgClosed k ∧ Countable k ∧ S ⊆ k := by
  let F := Subfield.closure S
  have hF : #F ≤ ℵ₀ :=
    (Subfield.cardinalMk_closure_le_max S).trans (max_le hS.lt_aleph0.le le_rfl)
  let A := algebraicClosure F K
  have hA : #A ≤ ℵ₀ := (Algebra.IsAlgebraic.cardinalMk_le_max F A).trans (max_le hF le_rfl)
  have hClosed : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  refine ⟨A.toSubfield, hClosed, Cardinal.mk_le_aleph0_iff.mp hA, ?_⟩
  intro x hx
  exact A.algebraMap_mem ⟨x, Subfield.subset_closure hx⟩

private theorem aeval_mem_subfield_of_coeff_mem {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    (D : Subfield Ω) (p : F[X]) (a : Ω) (ha : a ∈ D)
    (hp : ∀ i, algebraMap F Ω (p.coeff i) ∈ D) : aeval a p ∈ D := by
  rw [Polynomial.aeval_eq_sum_range]
  simp only [Algebra.smul_def]
  exact Subring.sum_mem D.toSubring fun i _ => mul_mem (hp i) (pow_mem ha i)

private theorem exists_countable_model_of_coefficients {K Ω : Type u} [Field K] [IsAlgClosed K]
    [Field Ω] [Algebra K Ω] (E : WeierstrassCurve K) [E.IsElliptic]
    (t : Ω) (C : Finset (rationalBase K t)) :
    ∃ (k : Subfield K) (_ : IsAlgClosed k) (_ : Countable k)
      (W : WeierstrassCurve k) (_ : W.IsElliptic),
        W.map (algebraMap k K) = E ∧ ∀ c ∈ C, (c : Ω) ∈ rationalBase k t := by
  classical
  have hrep (c : rationalBase K t) :
      ∃ P Q : K[X], (c : Ω) = aeval t P / aeval t Q :=
    (IntermediateField.mem_adjoin_simple_iff K (c : Ω)).mp c.2
  choose P Q hPQ using hrep
  let S : Set K := (⋃ c ∈ C, ((P c).coeffs : Set K) ∪ ((Q c).coeffs : Set K)) ∪
    {E.a₁, E.a₂, E.a₃, E.a₄, E.a₆}
  have hS : S.Finite := by
    refine Set.Finite.union (Set.Finite.biUnion C.finite_toSet fun c _ => ?_) (Set.toFinite _)
    exact ((P c).coeffs.finite_toSet).union ((Q c).coeffs.finite_toSet)
  obtain ⟨k, hkAlgClosed, hkCountable, hSk⟩ := exists_countable_algClosed_subfield S hS
  let W : WeierstrassCurve k :=
    ⟨⟨E.a₁, hSk (Or.inr (by simp))⟩, ⟨E.a₂, hSk (Or.inr (by simp))⟩,
      ⟨E.a₃, hSk (Or.inr (by simp))⟩, ⟨E.a₄, hSk (Or.inr (by simp))⟩,
      ⟨E.a₆, hSk (Or.inr (by simp))⟩⟩
  have hW : W.map (algebraMap k K) = E := by ext <;> rfl
  have hWell : W.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr fun h0 => E.isUnit_Δ.ne_zero ?_⟩
    rw [← hW, WeierstrassCurve.map_Δ, h0, map_zero]
  refine ⟨k, hkAlgClosed, hkCountable, W, hWell, hW, ?_⟩
  have heval (p : K[X]) (hp : (p.coeffs : Set K) ⊆ S) : aeval t p ∈ rationalBase k t := by
    refine aeval_mem_subfield_of_coeff_mem (rationalBase k t).toSubfield p t
      (IntermediateField.mem_adjoin_simple_self k t) fun i => ?_
    have hi : p.coeff i ∈ k := by
      by_cases h0 : p.coeff i = 0
      · rw [h0]
        exact zero_mem k
      · exact hSk (hp (Polynomial.coeff_mem_coeffs h0))
    let ci : k := ⟨p.coeff i, hi⟩
    change algebraMap K Ω (algebraMap k K ci) ∈ rationalBase k t
    rw [← IsScalarTower.algebraMap_apply k K Ω]
    exact (rationalBase k t).algebraMap_mem ci
  intro c hc
  rw [hPQ c]
  exact div_mem
    (heval (P c) fun _ hp => Or.inl (Set.mem_biUnion hc (Or.inl hp)))
    (heval (Q c) fun _ hq => Or.inl (Set.mem_biUnion hc (Or.inr hq)))

/-- Realize the curve and two coordinates of a finite extension of `K(t)` over one countable
algebraically closed subfield of `K`. The extension of constants recovers the upper field. -/
theorem exists_countable_cover_field {K Ω : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [Field Ω] [Algebra K Ω] (E : WeierstrassCurve K) [E.IsElliptic] (t : Ω)
    (L : IntermediateField (rationalBase K t) Ω) [FiniteDimensional (rationalBase K t) L]
    (s y : L) :
    ∃ (k : Subfield K) (_ : IsAlgClosed k) (_ : Countable k)
      (W : WeierstrassCurve k) (_ : W.IsElliptic),
      W.map (algebraMap k K) = E ∧
      ∃ (F : IntermediateField (rationalBase k t) Ω) (_ : FiniteDimensional (rationalBase k t) F),
        (∀ x ∈ F, x ∈ L) ∧ L ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω) ∧
          (s : Ω) ∈ F ∧ (y : Ω) ∈ F := by
  classical
  haveI : CharZero (rationalBase K t) :=
    charZero_of_injective_algebraMap (algebraMap K (rationalBase K t)).injective
  haveI : Algebra.IsSeparable (rationalBase K t) L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨a, ha⟩ := Field.exists_primitive_element (rationalBase K t) L
  set θ : Ω := (a : Ω)
  have hθ : IsIntegral (rationalBase K t) θ :=
    (IsIntegral.of_finite (rationalBase K t) a).map (IsScalarTower.toAlgHom (rationalBase K t) L Ω)
  have hLθ (x : Ω) (hx : x ∈ L) : x ∈ IntermediateField.adjoin (rationalBase K t) {θ} := by
    have h : (⟨x, hx⟩ : L) ∈ IntermediateField.adjoin (rationalBase K t) {a} :=
      ha ▸ IntermediateField.mem_top
    have hmap : x ∈ (IntermediateField.adjoin (rationalBase K t) {a}).map L.val := ⟨_, h, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at hmap
  have hexpr (x : L) : ∃ p : (rationalBase K t)[X], aeval θ p = (x : Ω) := by
    have h := hLθ (x : Ω) x.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθ.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  obtain ⟨rs, hrs⟩ := hexpr s
  obtain ⟨ry, hry⟩ := hexpr y
  let q := minpoly (rationalBase K t) θ
  let C := q.coeffs ∪ rs.coeffs ∪ ry.coeffs
  obtain ⟨k, hkAlgClosed, hkCountable, W, hWell, hW, hC⟩ :=
    exists_countable_model_of_coefficients E t C
  have hcoeff (p : (rationalBase K t)[X]) (hp : ∀ c ∈ p.coeffs, c ∈ C) (i : ℕ) :
      ((p.coeff i : rationalBase K t) : Ω) ∈ rationalBase k t := by
    by_cases h0 : p.coeff i = 0
    · rw [h0]
      exact zero_mem _
    · exact hC _ (hp _ (Polynomial.coeff_mem_coeffs h0))
  have hq := hcoeff q fun c hc => Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hθk : IsIntegral (rationalBase k t) θ := by
    let qΩ := q.map (algebraMap (rationalBase K t) Ω)
    have hqΩ : (qΩ.coeffs : Set Ω) ⊆ (rationalBase k t).toSubfield.toSubring := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hz
      rw [Polynomial.coeff_map]
      exact hq i
    let qk := qΩ.toSubring _ hqΩ
    refine ⟨qk, (Polynomial.monic_toSubring _ _ _).mpr ((minpoly.monic hθ).map _), ?_⟩
    have hmap : qk.map (algebraMap (rationalBase k t) Ω) = qΩ :=
      Polynomial.map_toSubring qΩ _ hqΩ
    rw [← Polynomial.eval_map, hmap, Polynomial.eval_map, ← aeval_def]
    exact minpoly.aeval _ _
  let F := IntermediateField.adjoin (rationalBase k t) {θ}
  have hθF : θ ∈ F := IntermediateField.mem_adjoin_simple_self _ θ
  have hFdim : FiniteDimensional (rationalBase k t) F :=
    IntermediateField.adjoin.finiteDimensional hθk
  have hbase : rationalBase k t ≤ (rationalBase K t).restrictScalars k :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.mem_adjoin_simple_self K t))
  let Lk : IntermediateField (rationalBase k t) Ω :=
    L.toSubfield.toIntermediateField fun c => L.algebraMap_mem ⟨c, hbase c.2⟩
  have hFL : F ≤ Lk := (IntermediateField.adjoin_simple_le_iff).mpr a.2
  have hLF : L ≤ IntermediateField.adjoin (rationalBase K t) (F : Set Ω) :=
    fun x hx => IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr hθF) (hLθ x hx)
  have hmemF (p : (rationalBase K t)[X]) (hp : ∀ c ∈ p.coeffs, c ∈ C) :
      aeval θ p ∈ F :=
    aeval_mem_subfield_of_coeff_mem F.toSubfield p θ hθF
      (fun i => F.algebraMap_mem ⟨_, hcoeff p hp i⟩)
  have hsF : (s : Ω) ∈ F := hrs ▸
    hmemF rs (fun c hc => Finset.mem_union_left _ (Finset.mem_union_right _ hc))
  have hyF : (y : Ω) ∈ F := hry ▸
    hmemF ry (fun c hc => Finset.mem_union_right _ hc)
  exact ⟨k, hkAlgClosed, hkCountable, W, hWell, hW, F, hFdim, fun _ hx => hFL hx, hLF, hsF, hyF⟩

end AbcAdaptation.Reference.Iut.Anabelian
